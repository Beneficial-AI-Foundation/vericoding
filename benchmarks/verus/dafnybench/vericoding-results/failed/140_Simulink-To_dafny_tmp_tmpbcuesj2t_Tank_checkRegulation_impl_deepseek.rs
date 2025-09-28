use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
enum Valve {
    ON,
    OFF,
}

struct Pipe {
    v1: Valve, // outlet valve 
    v2: Valve, // inlet Valve
    v3: Valve, // outlet valve
    in_flowv1: int, // flow in valve v1
    in_flowv2: int, // flow in valve v2
    in_flowv3: int, // flow in valve v3
}

impl Pipe {
    spec fn new() -> Self {
        Pipe {
            v1: Valve::OFF,
            v2: Valve::ON,
            v3: Valve::OFF,
            in_flowv1: 0,
            in_flowv2: 0,
            in_flowv3: 0,
        }
    }
}

struct Tank {
    pipe: Pipe,
    height: int,
}

impl Tank {
    spec fn new() -> Self {
        Tank {
            pipe: Pipe::new(),
            height: 0,
        }
    }
}

// <vc-helpers>
proof fn valve_flow_lemma(pipe: &Pipe)
    ensures
        pipe.v1 == Valve::ON ==> pipe.in_flowv1 > 0,
        pipe.v2 == Valve::ON ==> pipe.in_flowv2 > 0,
        pipe.v3 == Valve::ON ==> pipe.in_flowv3 > 0,
{
}

spec fn height_change_predicate(old_height: int, pipe: &Pipe) -> bool
{
    &&& pipe.v1 == Valve::OFF
    &&& pipe.v2 == Valve::ON
    &&& pipe.v3 == Valve::OFF
    ==> old_height > 0
}

proof fn height_change_lemma(old_height: int, pipe: &Pipe)
    requires
        pipe.v1 == Valve::OFF && pipe.v2 == Valve::ON && pipe.v3 == Valve::OFF,
    ensures
        old_height > 0,
{
}
// </vc-helpers>

// <vc-spec>
fn checkRegulation(tank: &mut Tank)
    ensures 
        (tank.height > 10 && tank.pipe.v1 == Valve::OFF && tank.pipe.v3 == Valve::ON && tank.pipe.v2 == old(tank).pipe.v2) 
        || (tank.height < 8 && tank.pipe.v1 == Valve::OFF && tank.pipe.v2 == Valve::ON && tank.pipe.v3 == old(tank).pipe.v3)
        || ((tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5) && tank.pipe.v2 == Valve::OFF && tank.pipe.v3 == old(tank).pipe.v3 && tank.pipe.v1 == old(tank).pipe.v1)
// </vc-spec>
// <vc-code>
{
    let old_height: int = tank.height;
    let old_pipe = *(&tank.pipe);
    
    if tank.height > 10 {
        tank.pipe.v1 = Valve::OFF;
        tank.pipe.v3 = Valve::ON;
        assert(tank.height > 10 && tank.pipe.v1 == Valve::OFF && tank.pipe.v3 == Valve::ON && tank.pipe.v2 == old_pipe.v2);
    } else if tank.height < 8 {
        tank.pipe.v1 = Valve::OFF;
        tank.pipe.v2 = Valve::ON;
        assert(tank.height < 8 && tank.pipe.v1 == Valve::OFF && tank.pipe.v2 == Valve::ON && tank.pipe.v3 == old_pipe.v3);
    } else if tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5 {
        tank.pipe.v2 = Valve::OFF;
        assert((tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5) && tank.pipe.v2 == Valve::OFF && tank.pipe.v3 == old_pipe.v3 && tank.pipe.v1 == old_pipe.v1);
    }
    
    proof {
        if tank.height > 10 {
            assert(tank.height > 10 && tank.pipe.v1 == Valve::OFF && tank.pipe.v3 == Valve::ON && tank.pipe.v2 == old_pipe.v2);
        } else if tank.height < 8 {
            assert(tank.height < 8 && tank.pipe.v1 == Valve::OFF && tank.pipe.v2 == Valve::ON && tank.pipe.v3 == old_pipe.v3);
        } else if tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5 {
            assert((tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5) && tank.pipe.v2 == Valve::OFF && tank.pipe.v3 == old_pipe.v3 && tank.pipe.v1 == old_pipe.v1);
        } else {
            assert(tank.height >= 8 && tank.height <= 10);
            assert(!(tank.pipe.in_flowv3 > 5) && !(tank.pipe.in_flowv1 > 5));
            assert(tank.pipe.v1 == old_pipe.v1 && tank.pipe.v2 == old_pipe.v2 && tank.pipe.v3 == old_pipe.v3);
        }
    }
}
// </vc-code>

fn main() {
}

}