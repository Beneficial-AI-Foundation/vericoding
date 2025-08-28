use vstd::prelude::*;

verus! {

// line contém uma string de tamanho l
// remover p caracteres a partir da posição at

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn delete(line: &mut Vec<char>, l: usize, at: usize, p: usize)
    requires
        l <= old(line).len(),
        at + p <= l,
    ensures
        line@ == old(line)@.subrange(0, at as int) + old(line)@.subrange((at + p) as int, l as int),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let ghost old_line = line@;
    
    // Remove p characters starting from position at
    // This is equivalent to moving elements from position at+p to position at
    let mut i = at;
    while i + p < l
        invariant
            at <= i <= l - p,
            i + p <= l,
            line@.len() == old_line.len(),
            line@.len() >= l,
            // Elements before 'at' are unchanged
            line@.subrange(0, at as int) == old_line.subrange(0, at as int),
            // Elements from 'i' onwards up to 'i+p' have been moved left by p positions
            line@.subrange(at as int, i as int) == old_line.subrange((at + p) as int, (i + p) as int),
            // Elements from 'i+p' onwards are unchanged
            line@.subrange((i + p) as int, l as int) == old_line.subrange((i + p) as int, l as int),
        decreases l - i
    {
        line[i] = line[i + p];
        i += 1;
        
        proof {
            assert(line@.subrange(0, at as int) == old_line.subrange(0, at as int));
            assert(line@[i - 1] == old_line[(i - 1) + p]);
            assert(line@.subrange(at as int, i as int) == old_line.subrange((at + p) as int, (i + p) as int));
            assert(line@.subrange((i + p) as int, l as int) == old_line.subrange((i + p) as int, l as int));
        }
    }
    
    proof {
        assert(line@.subrange(0, at as int) == old_line.subrange(0, at as int));
        assert(line@.subrange(at as int, i as int) == old_line.subrange((at + p) as int, (i + p) as int));
        assert(i == l - p);
        assert((i + p) as int == l as int);
        assert(line@.subrange(at as int, i as int) == old_line.subrange((at + p) as int, l as int));
        assert(line@.subrange(0, at as int) + line@.subrange(at as int, i as int) 
               == old_line.subrange(0, at as int) + old_line.subrange((at + p) as int, l as int));
    }
}
// </vc-code>

fn main() {
}

}