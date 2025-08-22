use vstd::prelude::*;

verus! {

// Precondition - always true (mimicking the Lean original)
pub open spec fn reverse_string_precond(s: Seq<char>) -> bool {
    true
}

// Recursive function to reverse a sequence (like the Lean reverseAux)
pub open spec fn reverse_aux(chars: Seq<char>, acc: Seq<char>) -> Seq<char>
    decreases chars.len()
{
    if chars.len() == 0 {
        acc
    } else {
        reverse_aux(chars.drop_first(), acc.push(chars.first()))
    }
}

// Main reverse function (mimicking the Lean reverseString)
pub open spec fn reverse_string_seq(s: Seq<char>) -> Seq<char>
{
    reverse_aux(s, Seq::<char>::empty())
}

// Postcondition specification (mimicking the Lean postcondition)
pub open spec fn reverse_string_postcond(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() == s.len() && result == s.reverse()
}

// Lemma about reverse_aux
proof fn reverse_aux_correct(chars: Seq<char>, acc: Seq<char>)
    ensures reverse_aux(chars, acc) == acc + chars.reverse()
    decreases chars.len()
{
    if chars.len() == 0 {
        assert(chars.reverse() == Seq::<char>::empty());
        assert(acc + Seq::<char>::empty() == acc);
    } else {
        let first = chars.first();
        let rest = chars.drop_first();
        
        // Inductive step
        reverse_aux_correct(rest, acc.push(first));
        
        // Show that chars.reverse() == rest.reverse().push(first)
        assert(chars == seq![first] + rest);
        assert(chars.reverse() == rest.reverse().push(first));
        
        // Show that acc.push(first) + rest.reverse() == acc + chars.reverse()
        assert(acc.push(first) + rest.reverse() == acc + seq![first] + rest.reverse());
        assert(acc + seq![first] + rest.reverse() == acc + (seq![first] + rest.reverse()));
        assert(seq![first] + rest.reverse() == chars.reverse());
    }
}

// The theorem (mimicking the Lean theorem, but we leave the proof incomplete like the original)
proof fn reverse_string_spec_satisfied(s: Seq<char>)
    requires reverse_string_precond(s)
    ensures reverse_string_postcond(s, reverse_string_seq(s))
{
    let result = reverse_string_seq(s);
    reverse_aux_correct(s, Seq::<char>::empty());
    
    assert(result == reverse_aux(s, Seq::<char>::empty()));
    assert(reverse_aux(s, Seq::<char>::empty()) == Seq::<char>::empty() + s.reverse());
    assert(Seq::<char>::empty() + s.reverse() == s.reverse());
    assert(result == s.reverse());
    assert(result.len() == s.reverse().len());
    assert(s.reverse().len() == s.len());
}

}

fn main() {}