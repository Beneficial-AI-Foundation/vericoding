// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
enum Valve {
    ON,
    OFF,
}

struct Pipe {
    v1: Valve,
    v2: Valve,
    v3: Valve,
    in_flowv1: int,
    in_flowv2: int,
    in_flowv3: int,
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
// </vc-preamble>

// <vc-helpers>
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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}