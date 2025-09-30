// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn rotation_split(len: usize, n: usize) -> (result: int) {
    len - (n % len)
}
// </vc-preamble>

// <vc-helpers>
proof fn subrange_push_index<T>(s: Seq<T>, a: int, i: int)
    requires
        0 <= a <= i,
        i < s.len()
    ensures
        s.subrange(a, i).push(s[i]) == s.subrange(a, i + 1)
{ }

proof fn add_push_assoc<T>(a: Seq<T>, b: Seq<T>, x: T)
    ensures
        a.add(b).push(x) == a.add(b.push(x))
{ }
// </vc-helpers>

// <vc-spec>
fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)

    requires
        list.len() > 0,

    ensures
        new_list.len() == list.len(),
        new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(
            list@.subrange(0, rotation_split(list.len(), n) as int),
        ),
// </vc-spec>
// <vc-code>
{
    let len = list.len();
    let s = len - (n % len);

    let mut v: Vec<u32> = Vec::new();

    let mut i = s;
    while i < len
        invariant
            list.len() == len,
            s <= i && i <= len,
            v.len() == i - s,
            v@ == list@.subrange(s as int, i as int),
            0 < len
        decreases (len - i) as int
    {
        v.push(list[i]);
        proof {
            subrange_push_index::<u32>(list@, s as int, i as int);
        }
        i += 1;
    }

    let mut j: usize = 0;
    while j < s
        invariant
            list.len() == len,
            j <= s && s <= len,
            v@ == list@.subrange(s as int, len as int).add(list@.subrange(0, j as int)),
            v.len() == (len - s) + j,
            0 < len
        decreases (s - j) as int
    {
        v.push(list[j]);
        proof {
            add_push_assoc::<u32>(list@.subrange(s as int, len as int), list@.subrange(0, j as int), list@[j as int]);
            subrange_push_index::<u32>(list@, 0, j as int);
        }
        j += 1;
    }

    proof {
        assert(s as int == rotation_split(len, n));
    }

    v
}
// </vc-code>

}
fn main() {}