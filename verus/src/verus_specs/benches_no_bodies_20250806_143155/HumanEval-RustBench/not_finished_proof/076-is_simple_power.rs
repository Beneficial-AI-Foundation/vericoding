use vstd::arithmetic::logarithm::log;
use vstd::arithmetic::power::pow;
use vstd::prelude::*;
verus! {
#[verifier::external_fn_specification]
fn ex_ilog(x: u32, base: u32) -> (ret: u32)
    requires
        x > 0,
        base > 1,
    ensures
        ret == log(base as int, x as int),
{
    return 0;  // TODO: Remove this line and implement the function body
}

#[verifier::external_fn_specification]
fn ex_checked_pow(x: u32, exp: u32) -> (ret: Option<u32>)
    ensures
        ret.is_some() <==> ret.unwrap() == pow(x as int, exp as nat),
        ret.is_none() <==> pow(x as int, exp as nat) > u32::MAX,
{
    return None;  // TODO: Remove this line and implement the function body
}

fn is_simple_power(x: u32, n: u32) -> (ret: bool)
    // pre-conditions-start
    requires
        x > 0,
        n > 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ret <==> x == pow(n as int, log(n as int, x as int) as nat),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

}
fn main() {}
