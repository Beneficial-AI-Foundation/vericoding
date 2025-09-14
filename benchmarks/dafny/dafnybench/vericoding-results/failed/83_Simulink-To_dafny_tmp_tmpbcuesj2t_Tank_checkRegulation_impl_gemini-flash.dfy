datatype Valve = ON | OFF

class Pipe{
   var v1: Valve; //outlet valve 
   var v2: Valve; //inlet Valve
   var v3: Valve; //outlet valve
   var in_flowv1: int; //flow in valve v1
   var in_flowv2: int; //flow in vave v2
   var in_flowv3: int; //flow in valve v3

   constructor()
   {
       this.v1:= OFF;
       this.v2:= ON;
   }

}
class Tank
{
   var pipe: Pipe;
   var height: int;
    constructor()
    {
        pipe := new Pipe();
    }
}

// <vc-helpers>
lemma ValveEquality(v1: Valve, v2: Valve)
  ensures (v1 == ON && v2 == ON) || (v1 == OFF && v2 == OFF) || (v1 == ON && v2 == OFF) || (v1 == OFF && v2 == ON)
{}
// </vc-helpers>

// <vc-spec>
method checkRegulation(tank: Tank)
 //requires tank.pipe.v1==OFF && tank.pipe.v2==ON && (tank.pipe.v3==OFF || tank.pipe.v2==ON) 
ensures (tank.height>10 && tank.pipe.v1==OFF && tank.pipe.v3==ON && tank.pipe.v2==old(tank.pipe.v2)) 
|| (tank.height <8 && tank.pipe.v1== OFF && tank.pipe.v2== ON && tank.pipe.v3==old(tank.pipe.v3))
|| ((tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5 ) && tank.pipe.v2==OFF && tank.pipe.v3==old(tank.pipe.v3) && tank.pipe.v1==old(tank.pipe.v1))
modifies tank.pipe;
// </vc-spec>
// <vc-code>
{
    var old_pipe_v2 := tank.pipe.v2;
    var old_pipe_v3 := tank.pipe.v3;
    var old_pipe_v1 := tank.pipe.v1;

    if (tank.height > 10) {
        tank.pipe.v1 := OFF;
        tank.pipe.v3 := ON;
    } else if (tank.height < 8) {
        tank.pipe.v1 := OFF;
        tank.pipe.v2 := ON;
    } else { // tank.height is between 8 and 10 inclusive
        if (tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5) {
            tank.pipe.v2 := OFF;
        } else {
            // This case needs to satisfy one of the postconditions.
            // As tank.height is not >10 and not <8, the first two postconditions
            // related to height are not directly met.
            // We need to ensure the third postcondition (related to flow and v2 being OFF)
            // or modify the tank state to meet another one.
            // Given the original postconditions, if we fall into this `else` branch
            // and neither of the flow conditions are met, then `tank.pipe.v2` would not be OFF
            // just by modifying `tank.pipe.v1` or `tank.pipe.v3`.
            // Let's try to achieve the third postcondition by setting v2 to OFF.
            tank.pipe.v2 := OFF;
        }
    }
}
// </vc-code>

