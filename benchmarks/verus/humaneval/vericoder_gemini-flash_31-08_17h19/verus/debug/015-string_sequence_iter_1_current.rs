use vstd::prelude::*;

verus! {

spec fn single_digit_number_to_char(n: nat) -> (result:char) {
    if n == 0 {
        '0'
    } else if n == 1 {
        '1'
    } else if n == 2 {
        '2'
    } else if n == 3 {
        '3'
    } else if n == 4 {
        '4'
    } else if n == 5 {
        '5'
    } else if n == 6 {
        '6'
    } else if n == 7 {
        '7'
    } else if n == 8 {
        '8'
    } else {
        '9'
    }
}
// pure-end
// pure-end

spec fn number_to_char(n: nat) -> (result:Seq<char>)
    decreases n,
{
    if (n == 0) {
        seq![]
    } else {
        number_to_char(n / 10).add(seq![single_digit_number_to_char(n % 10)])
    }
}
// pure-end
// pure-end

spec fn string_sequence(n: nat) -> (result:Seq<char>)
    decreases n,
{
    if n == 0 {
        seq!['0']
    } else {
        string_sequence((n - 1) as nat).add(seq![' '].add(number_to_char(n)))
    }
}
// pure-end

// <vc-helpers>
spec fn num_digits(n: nat) -> nat
    decreases n
{
    if n < 10 {
        1
    } else {
        1 + num_digits(n / 10)
    }
}

proof fn lemma_number_to_char_len(n: nat)
    ensures n == 0 ==> number_to_char(n).len() == 0,
            n > 0 ==> number_to_char(n).len() == num_digits(n),
{
    decreases n;
    if n == 0 {
        assert(number_to_char(n).len() == 0);
    } else if n < 10 {
        assert(number_to_char(n).len() == 1);
        assert(num_digits(n) == 1);
    } else {
        assert(number_to_char(n).len() == number_to_char(n / 10).len() + 1);
        lemma_number_to_char_len(n / 10);
        assert(number_to_char(n / 10).len() == num_digits(n / 10));
        assert(number_to_char(n).len() == num_digits(n / 10) + 1);
        assert(num_digits(n) == num_digits(n / 10) + 1);
    }
}

spec fn concat_seqs<A>(s1: Seq<A>, s2: Seq<A>) -> Seq<A> {
    s1.add(s2)
}

proof fn lemma_append_char(s: Seq<char>, c: char)
    ensures s.add(seq![c]).len() == s.len() + 1
{
    // This is directly provable from Seq.len() properties but good to have explicit lemma.
    assert(s.add(seq![c]).len() == s.len() + seq![c].len());
    assert(seq![c].len() == 1);
}
// </vc-helpers>

// <vc-spec>
fn string_sequence_impl(n: u8) -> (string_seq: Vec<char>)
    // post-conditions-start
    ensures
        string_seq@ == string_sequence(n as nat),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut string_seq_vec = Vec::new();
    let mut i: u8 = 0;

    if n == 0 {
        string_seq_vec.push('0');
    } else {
        // Initialize for i=0
        string_seq_vec.push('0');
        string_seq_vec.push(' ');

        // Loop for i from 1 to n
        i = 1;
        while i <= n
            invariant
                0 < i <= n + 1,
                string_seq_vec@ == string_sequence( (i-1) as nat).add(seq![' ']),
        {
            let mut num_str_vec: Vec<char> = Vec::new();
            let mut temp_num = i as nat;

            proof { lemma_number_to_char_len(temp_num); }

            let len_num_str = if temp_num == 0 { 0 } else { num_digits(temp_num) };
            
            // Build string for current number in reverse
            let mut j = 0;
            while temp_num > 0
                invariant
                    temp_num >= 0,
                    num_str_vec.len() == j,
                    j <= 9, // u8 max is 255, so max digits is 3. Max loop iterations is `num_digits(255)` which is 3.
                    number_to_char(i as nat).finite_seq_matches(num_str_vec@.map(|c| c as char)) == (temp_num == 0),
                    // This invariant links the constructed number string to the `number_to_char` spec function.
                    // It asserts that the *suffix* of `number_to_char(i)` corresponding to the remaining `temp_num`
                    // concatenated with the reversed digits collected so far (`num_str_vec`) matches the full `number_to_char(i)`.
                    number_to_char(i as nat) == 
                                            number_to_char(temp_num).add(num_str_vec@.view().reversed()),
            {
                let digit = (temp_num % 10) as nat;
                let char_digit = single_digit_number_to_char(digit);
                num_str_vec.push(char_digit);
                temp_num = temp_num / 10;
                j = j + 1;
            }

            proof {
                // If the number was 0 initially (only happens if i was 0, but loop starts at 1)
                if i as nat == 0 { /* handled by outer if */ } else {
                    // For non-zero numbers:
                    assert(num_str_vec@.view().len() == num_digits(i as nat));
                    assert(num_str_vec@.view().reversed() == number_to_char(i as nat));  // Prove the reversal gives the correct sequence
                }
            }


            string_seq_vec.extend_from_slice(&num_str_vec.as_slice().reversed());

            proof {
                let current_i_nat = i as nat;
                let prev_seq = string_sequence_vec@; // Before adding ' ' and number
                let next_val_seq = number_to_char(current_i_nat);

                // string_sequence_vec was `string_sequence((i-1) as nat).add(seq![' '])` initially
                // and after first extend, it's `string_sequence( (i-1) as nat).add(seq![' ']).add(number_to_char(i as nat))`
                assert(string_seq_vec@ == string_sequence((i-1) as nat).add(seq![' ']).add(number_to_char(current_i_nat)));

                // Here we need to assert that string_sequence_vec@, which is string_sequence((i-1) as nat) .add(seq![' ']) .add(number_to_char(i as nat))
                // matches string_sequence(i as nat) if the `string_seq_vec.push(' ');` (below) were already done.
                // It should be `string_sequence( (i-1) as nat) .add(seq![' ']) .add(number_to_char(i as nat)) .add(seq![' '])`
                // string_sequence(i) is string_sequence(i-1) .add(seq![' ']) .add(number_to_char(i))
                assert(string_sequence(current_i_nat) == string_sequence((current_i_nat - 1) as nat).add(seq![' ']).add(number_to_char(current_i_nat)));
            }

            if i < n {
                string_seq_vec.push(' ');
                proof {
                    // This asserts the invariant for the next iteration (i+1)
                    // The invariant for i+1 is: string_seq_vec@ == string_sequence(i as nat).add(seq![' '])
                    // And we have just made: string_seq_vec@ == string_sequence((i-1) as nat).add(seq![' ']).add(number_to_char(i as nat)).add(seq![' '])
                    // These two are definitionally equal
                    assert(string_sequence(i as nat).add(seq![' ']) == string_sequence((i-1) as nat).add(seq![' ']).add(number_to_char(i as nat)).add(seq![' ']));
                }
            }
            i = i + 1;
        }
        proof {
            // After loop, i == n + 1
            // Final string_seq_vec@ is expected to be string_sequence(n as nat)
            // Current string_seq_vec@ == string_sequence( (n) as nat).add(seq![' '])  -- from invariant, but there's no trailing space needed if i==n at the very end
            // The `if i < n` condition prevents the last space.
            assert(string_seq_vec@ == string_sequence(n as nat));
        }
    }

    string_seq_vec
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}