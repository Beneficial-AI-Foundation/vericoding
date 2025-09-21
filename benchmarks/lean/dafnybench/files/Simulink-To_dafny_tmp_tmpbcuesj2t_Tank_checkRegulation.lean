-- <vc-preamble>
inductive Valve
| ON
| OFF

structure Pipe where
v1: Valve  -- outlet valve
v2: Valve  -- inlet valve
v3: Valve  -- outlet valve
in_flowv1: Int  -- flow in valve v1
in_flowv2: Int  -- flow in valve v2
in_flowv3: Int  -- flow in valve v3

structure Tank where
pipe: Pipe
height: Int

def Pipe.init : Pipe := { 
    v1 := Valve.OFF
    v2 := Valve.ON
    v3 := Valve.OFF
    in_flowv1 := 0
    in_flowv2 := 0
    in_flowv3 := 0 
}

def Tank.init : Tank := { 
    pipe := Pipe.init
    height := 0 
}
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def checkRegulation (tank : Tank) : Tank :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem checkRegulation_spec (tank tank' : Tank) :
(tank'.height > 10 ∧ tank'.pipe.v1 = Valve.OFF ∧ tank'.pipe.v3 = Valve.ON ∧ tank'.pipe.v2 = tank.pipe.v2)
∨
(tank'.height < 8 ∧ tank'.pipe.v1 = Valve.OFF ∧ tank'.pipe.v2 = Valve.ON ∧ tank'.pipe.v3 = tank.pipe.v3)
∨
((tank'.pipe.in_flowv3 > 5 ∨ tank'.pipe.in_flowv1 > 5) ∧ tank'.pipe.v2 = Valve.OFF ∧ tank'.pipe.v3 = tank.pipe.v3 ∧ tank'.pipe.v1 = tank.pipe.v1)
:=
sorry
-- </vc-theorems>