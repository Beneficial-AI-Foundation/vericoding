use vstd::prelude::*;

verus! {

// <vc-helpers>
fn calculate_sr(n: u32) -> (r: u32)
    requires n >= 0,
    ensures (r as int) * (r as int) <= (n as int) < ((r as int) + 1) * ((r as int) + 1),
{
    let mut r: u32 = 0;
    let ghost n_int = n as int;
    let n64 = n as u64;
    while {
        let r64 = r as u64;
        (r64 * r64 <= n64) && (r < 65536)
    }
        invariant
            (r as int) * (r as int) <= n_int && r < 65536,
        decreases (n_int - (r as int) * (r as int)) as nat,
    {
        let next = r + 1;
        let next64 = next as u64;
        if next64 * next64 <= n64 {
            r = next;
        } else {
            break;
        }
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn mroot1(n: u32) -> (r: u32) //Cost O(root n)
    requires n >= 0,
    ensures r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
// </vc-spec>
// <vc-code>
{
    calculate_sr(n)
}
// </vc-code>

fn main() {}

}