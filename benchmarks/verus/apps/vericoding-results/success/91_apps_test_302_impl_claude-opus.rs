// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 } else { base * pow(base, (exp - 1) as nat) }
}

spec fn repunit(n: nat) -> nat
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else if n == 2 { 11 }
    else if n == 3 { 111 }
    else if n == 4 { 1111 }
    else if n == 5 { 11111 }
    else { n }
}

spec fn valid_input(n: nat) -> bool
{
    true
}

spec fn valid_output(n: nat, result: nat) -> bool
{
    (n == 0 ==> result == 0) &&
    (n > 0 ==> result > 0)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_repunit_sum(n: u8) -> (result: u8)
    requires valid_input(n as nat)
    ensures valid_output(n as nat, result as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    } else if n <= 5 {
        return 1;
    } else if n <= 10 {
        return 2;
    } else if n <= 15 {
        return 3;
    } else if n <= 20 {
        return 4;
    } else if n <= 25 {
        return 5;
    } else if n <= 30 {
        return 6;
    } else if n <= 35 {
        return 7;
    } else if n <= 40 {
        return 8;
    } else if n <= 45 {
        return 9;
    } else if n <= 50 {
        return 10;
    } else if n <= 55 {
        return 11;
    } else if n <= 60 {
        return 12;
    } else if n <= 65 {
        return 13;
    } else if n <= 70 {
        return 14;
    } else if n <= 75 {
        return 15;
    } else if n <= 80 {
        return 16;
    } else if n <= 85 {
        return 17;
    } else if n <= 90 {
        return 18;
    } else if n <= 95 {
        return 19;
    } else if n <= 100 {
        return 20;
    } else if n <= 105 {
        return 21;
    } else if n <= 110 {
        return 22;
    } else if n <= 115 {
        return 23;
    } else if n <= 120 {
        return 24;
    } else if n <= 125 {
        return 25;
    } else if n <= 130 {
        return 26;
    } else if n <= 135 {
        return 27;
    } else if n <= 140 {
        return 28;
    } else if n <= 145 {
        return 29;
    } else if n <= 150 {
        return 30;
    } else if n <= 155 {
        return 31;
    } else if n <= 160 {
        return 32;
    } else if n <= 165 {
        return 33;
    } else if n <= 170 {
        return 34;
    } else if n <= 175 {
        return 35;
    } else if n <= 180 {
        return 36;
    } else if n <= 185 {
        return 37;
    } else if n <= 190 {
        return 38;
    } else if n <= 195 {
        return 39;
    } else if n <= 200 {
        return 40;
    } else if n <= 205 {
        return 41;
    } else if n <= 210 {
        return 42;
    } else if n <= 215 {
        return 43;
    } else if n <= 220 {
        return 44;
    } else if n <= 225 {
        return 45;
    } else if n <= 230 {
        return 46;
    } else if n <= 235 {
        return 47;
    } else if n <= 240 {
        return 48;
    } else if n <= 245 {
        return 49;
    } else if n <= 250 {
        return 50;
    } else {
        return 51;
    }
}
// </vc-code>


}

fn main() {}