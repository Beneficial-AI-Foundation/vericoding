datatype Valve = ON | OFF

class Pipe{
   var v1: Valve //outlet valve 
   var v2: Valve //inlet Valve
   var v3: Valve //outlet valve
   var in_flowv1: int //flow in valve v1
   var in_flowv2: int //flow in vave v2
   var in_flowv3: int //flow in valve v3

// <vc-spec>
   constructor()
   {
       this.v1:= OFF;
       this.v2:= ON;
   }

}
class Tank
{
   var pipe: Pipe
   var height: int
    constructor()
    {
        pipe := new Pipe();
    }
}

// <vc-helpers>
// </vc-helpers>

method checkRegulation(tank: Tank)
 //requires tank.pipe.v1==OFF && tank.pipe.v2==ON && (tank.pipe.v3==OFF || tank.pipe.v2==ON) 
ensures (tank.height>10 && tank.pipe.v1==OFF && tank.pipe.v3==ON && tank.pipe.v2==old(tank.pipe.v2)) 
|| (tank.height <8 && tank.pipe.v1== OFF && tank.pipe.v2== ON && tank.pipe.v3==old(tank.pipe.v3))
|| ((tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5 ) && tank.pipe.v2==OFF && tank.pipe.v3==old(tank.pipe.v3) && tank.pipe.v1==old(tank.pipe.v1))
modifies tank.pipe
// </vc-spec>
// <vc-code>
{
  if (tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5) {
    // High flow condition - turn off inlet valve for safety
    tank.pipe.v2 := OFF;
  } else if (tank.height > 10) {
    // High water level - turn off outlet valve v1 and turn on outlet valve v3
    tank.pipe.v1 := OFF;
    tank.pipe.v3 := ON;
  } else {
    // For all other cases (including tank.height < 8 and 8 <= tank.height <= 10)
    // ensure outlet valve v1 is off and inlet valve v2 is on
    tank.pipe.v1 := OFF;
    tank.pipe.v2 := ON;
    // v3 remains unchanged
  }
}
// </vc-code>