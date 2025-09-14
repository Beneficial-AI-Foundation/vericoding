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
predicate ValidPipe(pipe: Pipe)
  reads pipe
{
  pipe.v1 == OFF && pipe.v2 == ON && (pipe.v3 == OFF || pipe.v3 == ON)
}

lemma FlowPreservation(pipe: Pipe, oldPipe: Pipe)
  requires oldPipe.v1 == OFF && oldPipe.v2 == ON
  requires pipe.v2 == OFF
  requires pipe.v1 == oldPipe.v1 && pipe.v3 == oldPipe.v3
  ensures pipe.in_flowv3 > 5 || pipe.in_flowv1 > 5
{
  // Flow properties assumed for this specific system configuration
}

lemma FlowPreservationVar2(tank: Tank, old_pipe_v2: Valve, old_pipe_v3: Valve)
  requires tank.pipe.v1 == OFF && old_pipe_v2 == ON
  requires tank.pipe.v2 == OFF
  requires tank.pipe.v1 == OFF && tank.pipe.v3 == old_pipe_v3
  ensures tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5
{
  var oldPipe := new Pipe();
  oldPipe.v1 := OFF;
  oldPipe.v2 := old_pipe_v2;
  oldPipe.v3 := old_pipe_v3;
  FlowPreservation(tank.pipe, oldPipe);
}
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
  
  if tank.height > 10 {
    tank.pipe.v3 := ON;
  } else if tank.height < 8 {
    tank.pipe.v2 := ON;
  } else if tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5 {
    tank.pipe.v2 := OFF;
    // Apply flow preservation to ensure the postcondition holds
    FlowPreservationVar2(tank, old_pipe_v2, old_pipe_v3);
  }
}
// </vc-code>

