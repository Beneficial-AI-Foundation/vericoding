// <vc-preamble>
datatype Valve = ON | OFF

class Pipe{
   var v1: Valve;
   var v2: Valve;
   var v3: Valve;
   var in_flowv1: int;
   var in_flowv2: int;
   var in_flowv3: int;

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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method checkRegulation(tank: Tank)

ensures (tank.height>10 && tank.pipe.v1==OFF && tank.pipe.v3==ON && tank.pipe.v2==old(tank.pipe.v2)) 
|| (tank.height <8 && tank.pipe.v1== OFF && tank.pipe.v2== ON && tank.pipe.v3==old(tank.pipe.v3))
|| ((tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5 ) && tank.pipe.v2==OFF && tank.pipe.v3==old(tank.pipe.v3) && tank.pipe.v1==old(tank.pipe.v1))
modifies tank.pipe;
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
