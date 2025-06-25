use vstd::prelude::*;

verus! {

pub enum Player {
    P1,
    P2,
}

impl Player {
    pub open spec fn other(self) -> Player {
        match self {
            Player::P1 => Player::P2,
            Player::P2 => Player::P1,
        }
    }
}

pub struct Variables {
    pub piles: Seq<nat>,
    pub turn: Player,
}

pub open spec fn init(v: Variables) -> bool {
    &&& v.piles.len() == 3
    &&& matches!(v.turn, Player::P1)
}

pub enum Step {
    TurnStep { take: nat, p: nat },
    NoOpStep,
}

pub open spec fn turn(v: Variables, v_prime: Variables, step: Step) -> bool
    recommends step matches Step::TurnStep { .. }
{
    let Step::TurnStep { p, take } = step;
    &&& p < v.piles.len()
    &&& take <= v.piles[p as int]
    &&& v_prime == Variables {
        piles: v.piles.update(p as int, v.piles[p as int] - take),
        turn: v.turn.other(),
    }
}

pub open spec fn next_step(v: Variables, v_prime: Variables, step: Step) -> bool {
    match step {
        Step::TurnStep { .. } => turn(v, v_prime, step),
        Step::NoOpStep => v_prime == v,
    }
}

pub proof fn next_step_deterministic_given_step(v: Variables, v_prime: Variables, v_prime_prime: Variables, step: Step)
    requires(next_step(v, v_prime, step))
    requires(next_step(v, v_prime_prime, step))
    ensures(v_prime == v_prime_prime)
{
}

pub open spec fn next(v: Variables, v_prime: Variables) -> bool {
    exists|step: Step| next_step(v, v_prime, step)
}

pub proof fn example_behavior() -> (b: Seq<Variables>)
    ensures(b.len() >= 3)
    ensures(init(b[0]))
    ensures(forall|i: nat| i + 1 < b.len() ==> next(b[i as int], b[(i + 1) as int]))
{
}

}