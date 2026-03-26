local computer = require('computer')
local component = require('component')

local event=require("event")
local filesystem = require("filesystem")
local serialization = require("serialization")
local shell=require("shell")
local term=require("term")
local table=require("table")
local sides = require("sides")

--sides API
--Bottom (bottom), Number: 0 down, negy
--Top (top), Number: 1 up, posy
--Back (back), Number: 2 north, negz
--Front (front), Number: 3 south, posz, forward
--Right (right), Number: 4 west, negx
--Left (left), Number: 5 east, posx

local neutronSourceRodBox=sides.posx --存放中子源的箱子相对于转置器的位置
local fuelRodBox=sides.posz --存放燃料棒的箱子相对于转置器的位置
local DepFuelRodBox=sides.negx --存放耗尽燃料棒的箱子相对于转置器的位置
local fuelName="HEP239" --燃料类型，可选项："HEAus" "HEP239" "HEU233" "HEP241" "HEA242" "HES"
local steamType="Normal" --蒸汽类型，可选项："UltraDense" "Normal"
local energyStorage="Leviathan" --储能方式，可选项："None" "SteamChannel" "Leviathan" "LeviathanSteamOutput" "EnergyStorageBlock" "capacitor"

local fixFluxRatio=1.0 --开机时(设定中子通量/可行的最大中子通量)的初始值，范围(0,1]
local minEnergyRatio=0.1 --给定储能方式最低电量比例，达到此容量时自动开机
local maxEnergyRatio=0.9 --给定储能方式最高电量比例，达到此容量时自动停机

local storageRod=sides.top --RBMK燃料储存棒相对于转置器的位置
local fuelRodRealRelativeCord={7,7} --填入实际想放入燃料棒（非中子源）的RBMK反应堆燃料棒位置，{7,7}为用扳手右键的位置
local controlRodSafe=0.0 --安全的控制棒位置
--local controlRodSafe=0.2264 --安全的控制棒位置，如果急停且初始位置1
local maxTempRatio=0.99 --燃料棒达到熔点比例，超过紧急停机
local maxColumnTempRatio=0.98 --燃料棒柱体达到熔点比例，超过紧急停机
local maxColumnTemp=1500  --燃料棒柱体最高温度
local maxFluxRatio=1.02 --燃料棒最高中子流量，超过紧急停机
local minFlux=26 --点火时最小中子流量
local controlHalflife=1 --控制常量，越小调整越快，但可能震荡
local minHalflife=10 --控制常量，限制中子通量的最大变化速度，越小变化越快

local minHalflifeLog=math.log(2.0)/minHalflife
local fuelMaxTemp=100


local PI =	3.14159265358979323846
local KEY_HEAT_PROVISION=0.2
local diffusion = 0.02
local gpu = component.gpu
local crane = component.rbmk_crane
local transposer = component.transposer
local console=component.rbmk_console

local origin={console.getRBMKPos()["rbmkCenterX"],console.getRBMKPos()["rbmkCenterZ"]}
local column_list={}
for i = 0, 14, 1 do
  for j = 0, 14, 1 do
    local columnData=console.getColumnData(i, j)
    if columnData~=nil then
      column_list[{i,j}]=columnData
    end
  end
end

local function getColumnDataSafe(pos)
  local data=console.getColumnData(pos[1], pos[2])--此方法不可靠，时不时出错误，需要包装
  local counter=0
  while data==nil and counter<=20 do
    os.sleep(0.01)
    data=console.getColumnData(pos[1], pos[2])
    counter=counter+1
  end
  if data==nil then
    error("Column "..tostring(pos[1])..","..tostring(pos[2]).." is nil")
  end
  return data
end

local neutronSourceRodRelativeCord={0,0}
local fuelRodRelativeCord={0,0}
local storageRodRelativeCord={0,0}
local list_controlRodRelativeCord={}
local controlRodCount=0
local list_fuelRods={}
local list_steamChannels={}
for key, value in pairs(column_list) do
  if value["type"]=="STORAGE" then
    storageRodRelativeCord=key
  end
  if value["type"]=="FUEL" then
    table.insert(list_fuelRods, key)
  end
  if value["type"]=="BOILER" then
    table.insert(list_steamChannels, key)
  end
  if value["type"]=="CONTROL" then
    table.insert(list_controlRodRelativeCord, key)
    controlRodCount=controlRodCount+1
  end
end

neutronSourceRodRelativeCord=list_fuelRods[1]
fuelRodRelativeCord=list_fuelRods[2]

if fuelRodRealRelativeCord[1]==neutronSourceRodRelativeCord[1] and fuelRodRealRelativeCord[2]==neutronSourceRodRelativeCord[2] then
  fuelRodRelativeCord,neutronSourceRodRelativeCord=neutronSourceRodRelativeCord,fuelRodRelativeCord
end

local function getCord(relativeCord)
  return {relativeCord[1]-7+origin[1],-(relativeCord[2]-7)+origin[2]}
end

local storageRodCord=getCord(storageRodRelativeCord)
local neutronSourceRodCord=getCord(neutronSourceRodRelativeCord)
local fuelRodCord=getCord(fuelRodRelativeCord)

local function clamp(x, min, max)
    if x < min then return min end
    if x > max then return max end
    return x
end

local function tableShallowCopy(t)
    local t2={}
    for k, v in pairs(t) do t2[k]=v end
    return t2
end

local list_fuelDep={}
local list_heatPerFlux={}
local list_fluxFunc={}
local list_fixFlux={}

--控制棒数:1
list_fuelDep["HEU233"]=0.602 --多少丰度抽出
list_heatPerFlux["HEU233"]=1.25 --每中子产热
local function HEU233Flux(enrichment) --中子放射函数
  return 27.5/100*(enrichment+math.sin(enrichment*PI)/3)
end
list_fluxFunc["HEU233"]=HEU233Flux
list_fixFlux["HEU233 UltraDense"]=578 --稳定温度:2805.1
list_fixFlux["HEU233 Normal"]=709 --稳定温度:2805.8

--控制棒数:1
list_fuelDep["HEP239"]=0.602 --多少丰度抽出,分解时更有性价比
list_heatPerFlux["HEP239"]=1.25 --每中子产热
local function HEP239Flux(enrichment) --中子放射函数
  return 30.0/100*(enrichment+math.sin(enrichment*PI)/3)
end
list_fluxFunc["HEP239"]=HEP239Flux
list_fixFlux["HEP239 UltraDense"]=502 --稳定温度:2689.1
list_fixFlux["HEP239 Normal"]=622 --稳定温度:2689.1

--控制棒数:2
list_fuelDep["HEAus"]=0.602 --多少丰度抽出
list_heatPerFlux["HEAus"]=1.5 --每中子产热
local function HEAusFlux(enrichment) --中子放射函数
  return 35.0/100*(enrichment+math.sin(enrichment*PI)/3)
end
list_fluxFunc["HEAus"]=HEAusFlux
list_fixFlux["HEAus UltraDense"]=772 --稳定温度:5100.7
list_fixFlux["HEAus Normal"]=858 --稳定温度:5104.2

--控制棒数:2
list_fuelDep["HEP241"]=0.602 --多少丰度抽出
list_heatPerFlux["HEP241"]=1.75 --每中子产热
local function HEP241Flux(enrichment) --中子放射函数
  return 40.0/100*(enrichment+math.sin(enrichment*PI)/3)
end
list_fluxFunc["HEP241"]=HEP241Flux
list_fixFlux["HEP241 UltraDense"]=269 --稳定温度:2688.8
list_fixFlux["HEP241 Normal"]=333 --稳定温度:2686.7

--控制棒数:2
list_fuelDep["HEA242"]=0.602 --多少丰度抽出
list_heatPerFlux["HEA242"]=2.0 --每中子产热
local function HEA242Flux(enrichment) --中子放射函数
  return 45.0/100*(enrichment+math.sin(enrichment*PI)/3)
end
list_fluxFunc["HEA242"]=HEA242Flux
list_fixFlux["HEA242 UltraDense"]=174 --稳定温度:2336.4
list_fixFlux["HEA242 Normal"]=224 --稳定温度:2336.3

--控制棒数:3,需要钋210中子源
list_fuelDep["HES"]=0.602 --多少丰度抽出
list_heatPerFlux["HES"]=1.75 --每中子产热
local function HESFlux(enrichment) --中子放射函数
  return 90.0/100*(enrichment)
end
list_fluxFunc["HES"]=HESFlux
list_fixFlux["HES UltraDense"]=134 --稳定温度:2940.3
list_fixFlux["HES Normal"]=162.5 --稳定温度:2938.8

local fuelDep=list_fuelDep[fuelName]
local heatPerFlux=list_heatPerFlux[fuelName]
local fluxFunc=list_fluxFunc[fuelName]
local fixFluxMax=list_fixFlux[fuelName.." "..steamType] --最大中子通量
local fixFlux=fixFluxMax*fixFluxRatio
local fixFlux_patch=1

local function burnAndUpdateHeat(influx,enrichment,hpf,coreHeat,hullHeat)
  if influx==0 then
    return 20
  end
  local coreHeatNow=clamp(coreHeat+fluxFunc(enrichment)*influx*hpf,20,1000000)
  if coreHeatNow>hullHeat then
    local mid=(coreHeatNow-hullHeat)*0.5
    return clamp(hullHeat+mid*diffusion,20,1000000)
  else
    return hullHeat
  end
end

local function sameValueArray(value,length)
  local list_value={}
  for i = 1, length, 1 do
    list_value[i]=value
  end
  return list_value
end

local function controlRodLevelRange(enrichment)
  local flux=fluxFunc(enrichment)
  local balance=clamp((1/flux + controlRodCount -4)/controlRodCount,0,1)
  local eps=minHalflifeLog/flux*0.05/controlRodCount
  return balance,eps
end

local function controlRodLevel(targetFlux,flux,enrichment)
  local u=(targetFlux-flux)/clamp(flux,10,10*fixFluxMax)
  local balance,eps=controlRodLevelRange(enrichment)
  local level=balance+eps*clamp(u*minHalflife/controlHalflife,-1,1)
  return sameValueArray(level,controlRodCount),sameValueArray(balance,controlRodCount),sameValueArray(eps,controlRodCount)
end

local function safeControlRod()
  return sameValueArray(controlRodSafe,controlRodCount)
end

local craneState="idle"

local transposerMoved=false
local craneWait=0
local function craneIdle()
  craneWait=0
  transposerMoved=false
  return
end

local function craneWaitAndLoad()
  if craneWait<=0 then
    crane.load()
    craneWait=21
  end
  craneWait=craneWait-1
end

local unloadBox=0
local function unloadToStorage()
  if crane.getXenonPoison()=="N/A" then
    if transposer.getStackInSlot(storageRod,1)~=nil then
      if transposer.transferItem(storageRod, unloadBox, 1, 1) == 0 then
        error("can not unload")
      end
      craneState="idle"
    end
  else
    craneWaitAndLoad()
  end
end

local loadBox=0
local function loadFromStorage()
  if crane.getXenonPoison()=="N/A" then
    if transposerMoved then
      craneWaitAndLoad()
    else
      local item_list = transposer.getAllStacks(loadBox).getAll()
      for key, value in pairs(item_list) do
          if value["name"] ~= nil then
            if transposer.transferItem(loadBox, storageRod, 1 , key + 1 , 1) == 0 then
              error("can not load")
            end
            transposerMoved=true
          break
        end
      end
    end
  else
    craneState="idle"
  end
end

local function unloadToFuelRod()
  if crane.getXenonPoison()=="N/A" then
    craneState="idle"
  else
    craneWaitAndLoad()
  end
end

local function loadFromFuelRod()
  if crane.getXenonPoison()=="N/A" then
    craneWaitAndLoad()
  else
    craneState="idle"
  end
end

local craneDirection=0
local craneLastMoveDirection=0
local craneMove_ctbl={
  [1]="right",
  [2]="down",
  [3]="left",
  [4]="up"
}

local craneTargetCord={crane.getCranePos()}
local craneLastCord={crane.getCranePos()}
local cranePos={crane.getCranePos()}
local craneGuessCord={crane.getCranePos()}
local function moveToTarget()
  local tol=0.075
  if craneLastCord[1]~=cranePos[1] then
    craneGuessCord[1]=(craneLastCord[1]+cranePos[1])*0.5
    if cranePos[1]>craneLastCord[1] then
      craneDirection=(craneLastMoveDirection-1)%4
    else
      craneDirection=(craneLastMoveDirection-3)%4
    end
  end
  if craneLastCord[2]~=cranePos[2] then
    craneGuessCord[2]=(craneLastCord[2]+cranePos[2])*0.5
    if cranePos[2]>craneLastCord[2] then
      craneDirection=(craneLastMoveDirection-2)%4
    else
      craneDirection=(craneLastMoveDirection-4)%4
    end
  end
  if math.abs(cranePos[1]-craneGuessCord[1])>0.6 then
    craneGuessCord[1]=cranePos[1]
  end
  if math.abs(cranePos[2]-craneGuessCord[2])>0.6 then
    craneGuessCord[2]=cranePos[2]
  end
  if craneGuessCord[1]<craneTargetCord[1]-tol then
    craneLastMoveDirection=1+(0+craneDirection)%4
    crane.move(craneMove_ctbl[craneLastMoveDirection])
    craneGuessCord[1]=craneGuessCord[1]+0.05
  elseif craneGuessCord[2]<craneTargetCord[2]-tol then
    craneLastMoveDirection=1+(1+craneDirection)%4
    crane.move(craneMove_ctbl[craneLastMoveDirection])
    craneGuessCord[2]=craneGuessCord[2]+0.05
  elseif craneGuessCord[1]>craneTargetCord[1]+tol then
    craneLastMoveDirection=1+(2+craneDirection)%4
    crane.move(craneMove_ctbl[craneLastMoveDirection])
    craneGuessCord[1]=craneGuessCord[1]-0.05
  elseif craneGuessCord[2]>craneTargetCord[2]+tol then
    craneLastMoveDirection=1+(3+craneDirection)%4
    crane.move(craneMove_ctbl[craneLastMoveDirection])
    craneGuessCord[2]=craneGuessCord[2]-0.05
  else
    craneState="idle"
  end
end

local function ifCraneReach()
  local tol=0.075*1.1
  return (math.abs(craneGuessCord[1]-craneTargetCord[1])<tol) and (math.abs(craneGuessCord[2]-craneTargetCord[2])<tol)
end

local crane_ctbl=
{
  ["idle"]=craneIdle,
  ["unload to storage rod"]=unloadToStorage,
  ["load from storage rod"]=loadFromStorage,
  ["unload to fuel rod"]=unloadToFuelRod,
  ["load from fuel rod"]=loadFromFuelRod,
  ["move to target position"]=moveToTarget
}

local state="idle"
local additionalInfo=""
local command="s"

local fuelRodDataNow={}
local fuelRodTempNow=20
local fuelRodSkinTempNow=20
local RealFuelRodSkinTempNow=20 --实际参与融毁判定的
local fuelRodCoreTempNow=20
local enrichmentNow=1
local xenonPoisonNow=0
local fluxNow=0
local whereToPutFuel=DepFuelRodBox
local controlRodLevelNow={}
local function getLevels()
  for i = 1, controlRodCount, 1 do
    controlRodLevelNow[i]=getColumnDataSafe(list_controlRodRelativeCord[i])["level"]
  end
end
getLevels()
local setLevel=tableShallowCopy(controlRodLevelNow)

local list_energyRatio={}

local steamChannelMax=1000000
local function steamRatio()
  local steam=0
  for key, value in pairs(list_steamChannels) do
    steam=math.max(steam,getColumnDataSafe(value)["steam"]/steamChannelMax)
  end
  return steam
end
list_energyRatio["SteamChannel"]=steamRatio

local LeviathanMaxEnergy=100000000000
local function LeviathanEnergyRatio()
  return component.ntm_turbine.getPower()/LeviathanMaxEnergy
end
list_energyRatio["Leviathan"]=LeviathanEnergyRatio

local function LeviathanSteamOutputRatio()
  local _,_,now,max=component.ntm_turbine.getFluid()
  return now/max
end
list_energyRatio["LeviathanSteamOutput"]=LeviathanSteamOutputRatio

local function noEnergyStorage()
  return 0
end
list_energyRatio["None"]=noEnergyStorage

local function EnergyStorageBlockRatio()
  local now,max=component.ntm_energy_storage.getEnergyInfo()
  return now/max
end
list_energyRatio["EnergyStorageBlock"]=EnergyStorageBlockRatio

local function capacitorRatio()
  return component.capacitor.getEnergy()/component.capacitor.getMaxEnergy()
end
list_energyRatio["capacitor"]=capacitorRatio

local energyRatio=list_energyRatio[energyStorage]
local energyRatioNow=energyRatio()

local function ifEnergyStorageFull()
  return energyRatioNow>maxEnergyRatio
end

local function ifEnergyStorageEmpty()
  return energyRatioNow<minEnergyRatio
end


local function controlRodSetLevel()
  for i = 1, controlRodCount, 1 do
    console.setColumnLevel(list_controlRodRelativeCord[i][1],list_controlRodRelativeCord[i][2],setLevel[i])
  end
end

local function ifControlRodReach(eps)
  local ret=true
  for i = 1, controlRodCount, 1 do
    ret=(ret and (math.abs(controlRodLevelNow[i]-setLevel[i])<eps[i]*0.5))
  end
  return ret
end

local function idle()
  if command=="r" and ifEnergyStorageEmpty() then
    additionalInfo=""
    state="load fuel rod"
  end
end

local function loadFuelRod()
  if additionalInfo=="" then
    craneTargetCord=storageRodCord
    craneState="move to target position"
    additionalInfo="moving crane to storage rod"
  elseif additionalInfo=="moving crane to storage rod" then
    if craneState=="idle" then
      loadBox=fuelRodBox
      craneState="load from storage rod"
      additionalInfo="loading fuel rod to crane"
    end
  elseif additionalInfo=="loading fuel rod to crane" then
    local dep=crane.getDepletion()
    if dep~="N/A" then
      local level,balance,eps=controlRodLevel(1,1,dep)
      setLevel=tableShallowCopy(balance)
    end
    if craneState=="idle" then
      craneTargetCord=fuelRodCord
      craneState="move to target position"
      additionalInfo="moving crane to fuel rod"
    end
  elseif additionalInfo=="moving crane to fuel rod" then
    local dep=crane.getDepletion()
    if dep~="N/A" then
      local level,balance,eps=controlRodLevel(1,1,dep)
      setLevel=tableShallowCopy(balance)
    end
    if craneState=="idle" then
      craneState="unload to fuel rod"
      additionalInfo="unloading crane to fuel rod"
    end
  elseif additionalInfo=="unloading crane to fuel rod" then
    if craneState=="idle" then
      additionalInfo=""
      state="control rod initialize"
    end
  else
    error("unknown sub state")
  end
end

local function controlRodInitialize()
  if enrichmentNow~="N/A" and enrichmentNow~=0 then
    local level,balance,eps=controlRodLevel(1,1,enrichmentNow)
    setLevel=tableShallowCopy(balance)
    additionalInfo=""
    state="neutron source ignition"
  end
end

local function neutronSourceStartReaction()
  local level,balance,eps=controlRodLevel(1,1,enrichmentNow)
  setLevel=tableShallowCopy(balance)
  if additionalInfo=="" then
    craneTargetCord=storageRodCord
    craneState="move to target position"
    additionalInfo="moving crane to storage rod"
  elseif additionalInfo=="moving crane to storage rod" then
    if craneState=="idle" then
      loadBox=neutronSourceRodBox
      craneState="load from storage rod"
      additionalInfo="loading neutron source to crane"
    end
  elseif additionalInfo=="loading neutron source to crane" then
    if craneState=="idle" then
      craneTargetCord=neutronSourceRodCord
      craneState="move to target position"
      additionalInfo="moving crane to neutron source"
    end
  elseif additionalInfo=="moving crane to neutron source" then
    if craneState=="idle" and ifControlRodReach(eps) then
      craneState="unload to fuel rod"
      additionalInfo="unloading crane to neutron source rod"
    end
  elseif additionalInfo=="unloading crane to neutron source rod" then
    if craneState=="idle" then
      additionalInfo="ignition"
    end
  elseif additionalInfo=="ignition" then
    if xenonPoisonNow==0 and fluxNow>minFlux then
      additionalInfo="control rod to self-sustained level"
    end
  elseif additionalInfo=="control rod to self-sustained level" then
    if ifControlRodReach(eps) then
      craneState="load from fuel rod"
      additionalInfo="loading crane from neutron source rod"
    end
  elseif additionalInfo=="loading crane from neutron source rod" then
    if craneState=="idle" then
      additionalInfo=""
      state="running"
    end
  else
    error("unknown sub state")
  end
end

local function running()
  if not(enrichmentNow=="N/A") then
    local level,balance,eps=controlRodLevel(fixFlux_patch*fixFlux,fluxNow,enrichmentNow)
    setLevel=tableShallowCopy(level)
  else
    error("no fuel rod")
  end

  if fuelRodTempNow>maxColumnTemp*maxColumnTempRatio then
    state="Emergency SHUTDOWN"
    additionalInfo="fuel rod column too hot:"..tostring(fuelRodTempNow)
    return
  end
  if RealFuelRodSkinTempNow>fuelMaxTemp*maxTempRatio then
    state="Emergency SHUTDOWN"
    additionalInfo="fuel rod skin too hot:"..tostring(RealFuelRodSkinTempNow)
    return
  end
  if fluxNow>fixFluxMax*maxFluxRatio*fixFlux_patch then
    state="Emergency SHUTDOWN"
    additionalInfo="flux too high:"..tostring(fluxNow)
    return
  end

  if additionalInfo=="" then
    craneTargetCord=storageRodCord
    craneState="move to target position"
    additionalInfo="moving crane to storage rod"
  elseif additionalInfo=="moving crane to storage rod" then
    if craneState=="idle" then
      unloadBox=neutronSourceRodBox
      craneState="unload to storage rod"
      additionalInfo="unloading neutron source"
    end
  elseif additionalInfo=="unloading neutron source" then
    if craneState=="idle" then
      craneTargetCord=fuelRodCord
      craneState="move to target position"
      additionalInfo="moving crane to fuel rod"
    end
  elseif additionalInfo=="moving crane to fuel rod" then
    if craneState=="idle" then
      additionalInfo="ready to SHUTDOWN"
    end
  elseif additionalInfo=="ready to SHUTDOWN" then
    if not(ifCraneReach()) then
      craneTargetCord=fuelRodCord
      craneState="move to target position"
      additionalInfo="moving crane to fuel rod"
    end
    if enrichmentNow<fuelDep or ifEnergyStorageFull() or command=="s" or command=="x" then
      whereToPutFuel=DepFuelRodBox
      if enrichmentNow>=fuelDep then
        whereToPutFuel=fuelRodBox
      end
      additionalInfo=""
      state="fuel rod cooling"
    end
  else
    error("unknown sub state")
  end
end

local function cooling()
  setLevel=safeControlRod()
  if fuelRodCoreTempNow<40 then
    additionalInfo=""
    state="remove fuel rod"
  end
end

local function removeFuelRod()
  if additionalInfo=="" then
    craneState="load from fuel rod"
    additionalInfo="loading crane from fuel rod"
  elseif additionalInfo=="loading crane from fuel rod" then
    if craneState=="idle" then
      craneTargetCord=storageRodCord
      craneState="move to target position"
      additionalInfo="moving crane to storage rod"
    end
  elseif additionalInfo=="moving crane to storage rod" then
    if craneState=="idle" then
      unloadBox=whereToPutFuel
      craneState="unload to storage rod"
      additionalInfo="unloading fuel rod"
    end
  elseif additionalInfo=="unloading fuel rod" then
    if craneState=="idle" then
      additionalInfo=""
      state="idle"
    end
  else
    error("unknown sub state")
  end
end

local function ifShuttingdown()
  local result
  local err,errinfo=pcall(function ()
    result=(getColumnDataSafe(fuelRodRelativeCord)["coreMaxTemp"]~=0)
  end)
  if err then
    return result
  else
    return true
  end
end
--可能应该只依靠控制棒，但既然只有1个燃料棒，何乐而不为呢
local function shutdown()
  setLevel=safeControlRod()
  controlRodSetLevel()
  if ifShuttingdown() then
    if craneState=="idle" then
      if crane.getXenonPoison()=="N/A" then
        craneTargetCord=fuelRodCord
        if ifCraneReach() then
          craneState="load from fuel rod"
        else
          craneState="move to target position"
        end
      end
    end
  end
end

local state_ctbl=
{
  ["idle"]=idle,
  ["load fuel rod"]=loadFuelRod,
  ["control rod initialize"]=controlRodInitialize,
  ["neutron source ignition"]=neutronSourceStartReaction,
  ["running"]=running,
  ["fuel rod cooling"]=cooling,
  ["remove fuel rod"]=removeFuelRod,
  ["Emergency SHUTDOWN"]=shutdown
}

local w1, h1 = gpu.getViewport()

local inputting=false
local inputString=""
local function keyDown(_,_,key)
  if inputting then
    if string.char(key)=="i" then inputting=false
    elseif string.char(key)=="\r" then
      if tonumber(inputString)~=nil then
        fixFluxRatio=clamp(tonumber(inputString),0,1)
      end
      inputting=false
    else inputString=inputString..string.char(key)
    end
  else
    if key==115 then command="s"
    elseif key==114 then command="r"
    elseif key==120 then command="x"
    elseif string.char(key)=="i" then inputting=true inputString=""
    end
  end
end
event.listen("key_down",keyDown)

local yieldTime -- variable to store the time of the last yield
local function yield()
  if yieldTime then -- check if it already yielded
    if os.clock() - yieldTime > 2 then -- if it were more than 2 seconds since the last yield
      computer.pushSignal("someFakeEvent") -- queue the event
      event.pull(10,"someFakeEvent") -- pull it
      yieldTime = nil -- reset the counter
    end
  else
      yieldTime = os.clock() -- store the time
  end
end

local tickcount=0
local tpc=1

local function main_rc()
  while true do
    craneLastCord=cranePos
    cranePos={crane.getCranePos()}
    fuelRodDataNow=getColumnDataSafe(fuelRodRelativeCord)
    getLevels()
    energyRatioNow=energyRatio()
    fuelRodTempNow=fuelRodDataNow["hullTemp"]
    fuelRodSkinTempNow=fuelRodDataNow["coreSkinTemp"]
    fuelRodCoreTempNow=fuelRodDataNow["coreTemp"]
    fuelMaxTemp=fuelRodDataNow["coreMaxTemp"]
    enrichmentNow=fuelRodDataNow["enrichment"]
    xenonPoisonNow=fuelRodDataNow["xenon"]
    fluxNow=fuelRodDataNow["fluxQuantity"]
    RealFuelRodSkinTempNow=burnAndUpdateHeat(fluxNow,enrichmentNow,heatPerFlux,fuelRodCoreTempNow,fuelRodSkinTempNow)
    --实际参与融毁判定的，直接显示的表面温度并不参与融毁判定
    fixFlux=fixFluxMax*fixFluxRatio
    if type(enrichmentNow)=="number" and enrichmentNow~=0 then
      fixFlux_patch=fluxFunc(1)/fluxFunc(enrichmentNow)
    else
      fixFlux_patch=1
    end


    local tickcountNow=math.floor(os.time()*1000/60/60+0.5)
    tpc=tickcountNow-tickcount
    tickcount=tickcountNow

    local scBuffer="Reactor state: "..state..", "..additionalInfo.."\n"
    scBuffer=scBuffer.."Crane state: "..craneState.."\n"
    scBuffer=scBuffer.."fuel Rod temp: "..tostring(fuelRodTempNow).."/"..tostring(maxColumnTemp).."\n"
    scBuffer=scBuffer.."fuel Rod skin temp: "..tostring(RealFuelRodSkinTempNow).."/"..tostring(fuelMaxTemp).."\n"
    scBuffer=scBuffer.."flux in: "..tostring(fluxNow).."\n"
    scBuffer=scBuffer.."target flux: "..tostring(fixFlux_patch*fixFlux).."/"..tostring(fixFlux).."(full enrichment)".."\n"
    scBuffer=scBuffer.."target flux/max flux(press i to edit): "..tostring(fixFluxRatio).."\n"
    scBuffer=scBuffer.."control rod level: "..tostring(controlRodLevelNow[1]).."\n"
    scBuffer=scBuffer.."enrichment: "..tostring(enrichmentNow).."\n"
    scBuffer=scBuffer.."energy storage percentage: "..tostring(100*energyRatioNow).."%".."\n"
    scBuffer=scBuffer.."ticks per cycle: "..tostring(tpc).."\n"
    scBuffer=scBuffer.."[Run] [Stop] [eXit] "..command.."\n"
    if inputting then
      scBuffer=scBuffer.."input string:"..inputString.."\n"
      scBuffer=scBuffer.."press enter to enter,press i to exit".."\n"
    end

    term.clear()
    term.write(scBuffer)
    os.sleep(0.01)

    state_ctbl[state]()
    crane_ctbl[craneState]()
    controlRodSetLevel()

    --yield() --Avoiding "Too long without yielding"
    if command=="x" and (state=="idle" or state=="Emergency SHUTDOWN") then
      break
    end
  end
  shell.execute("resolution "..w1.." "..h1)
end

local err,errinfo=pcall(main_rc)
if err then
  os.sleep(0.01)
else
  print(errinfo)
  while ifShuttingdown() do
    shutdown()
    crane_ctbl[craneState]()
    os.sleep(0.01)
  end
end
