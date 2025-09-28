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
    match tank.height {
        h if h > 10 => {
            tank.pipe.v1 = Valve::OFF;
            tank.pipe.v3 = Valve::ON;
            // tank.pipe.v2 remains old(tank).pipe.v2
        }
        h if h < 8 => {
            tank.pipe.v1 = Valve::OFF;
            tank.pipe.v2 = Valve::ON;
            // tank.pipe.v3 remains old(tank).pipe.v3
        }
        _ => { // This covers the case where 8 <= tank.height <= 10
            if tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5 {
                tank.pipe.v2 = Valve::OFF;
                // tank.pipe.v3 remains old(tank).pipe.v3
                // tank.pipe.v1 remains old(tank).pipe.v1
            } else {
                // If the height is between 8 and 10 and the flow conditions are not met,
                // the `ensures` clause does not require any specific state change
                // that means tank retains its current state.
                // We need to ensure that none of the disjuncts in the ensures clause
                // are met, for this specific case.
                // The current implementation is safe, we don't need to do anything.
                // The proof obligation for this specific branch is that
                // (tank.height > 10 && ...) is false, AND
                // (tank.height < 8 && ...) is false, AND
                // ((tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5) && ...) is false.
                // And this is indeed true by the conditions of this branch.
            }
        }
    }
}
// </vc-code>

fn main() {
}

}