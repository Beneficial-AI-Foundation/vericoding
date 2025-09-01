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
    } else if n > 0 && n < 10 {
        assert(number_to_char(n).len() == 1);
        assert(num_digits(n) == 1);
    } else if n >= 10 {
        assert(number_to_char(n).len() == (number_to_char(n / 10).len() + 1));
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

proof fn lemma_number_to_char_reversed_correct(num: nat)
    ensures (num > 0 ==> {
        let mut temp_num = num;
        let mut num_str_seq = Seq::empty();
        while temp_num > 0
            invariant
                temp_num >= 0,
                num_str_seq.view().reversed().add(number_to_char(temp_num)) == number_to_char(num),
            decreases temp_num,
        {
            let digit = (temp_num % 10) as nat;
            let char_digit = single_digit_number_to_char(digit);
            num_str_seq = num_str_seq.add(seq![char_digit]);
            temp_num = temp_num / 10;
        }
        num_str_seq.view().reversed() == number_to_char(num)
    })
    decreases num
{
    if num > 0 {
        lemma_number_to_char_len(num);
        let mut temp_num = num;
        let mut num_str_seq = Seq::empty();
        while temp_num > 0 {
            let digit = (temp_num % 10) as nat;
            let char_digit = single_digit_number_to_char(digit);
            num_str_seq = num_str_seq.add(seq![char_digit]);
            temp_num = temp_num / 10;
        }
    }
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

    if n == 0 {
        string_seq_vec.push('0');
    } else {
        // Initialize for i=0
        string_seq_vec.push('0');

        // Loop for i from 1 to n
        let mut i: u8 = 1;
        while i <= n
            invariant
                0 < i <= n + 1,
                string_seq_vec@ == string_sequence((i - 1) as nat),
        {
            // add space before the number
            string_seq_vec.push(' ');
            
            let current_i_nat = i as nat;
            let mut num_str_vec: Vec<char> = Vec::new();
            let mut temp_num = current_i_nat;

            proof { lemma_number_to_char_len(current_i_nat); }
            
            // Build string for current number in reverse
            while temp_num > 0
                invariant
                    temp_num >= 0,
                    num_str_vec@.view().reversed().add(number_to_char(temp_num)) == number_to_char(current_i_nat),
                decreases temp_num,
            {
                let digit = (temp_num % 10) as nat;
                let char_digit = single_digit_number_to_char(digit);
                num_str_vec.push(char_digit);
                temp_num = temp_num / 10;
            }

            proof {
                assert(num_str_vec@.view().reversed() == number_to_char(current_i_nat)) by {
                    lemma_number_to_char_reversed_correct(current_i_nat);
                };
            }

            let num_str_len = num_str_vec.len();
            let mut reversed_num_str_vec = Vec::new();
            let mut k: int = (num_str_len as int) - 1;
            while k >= 0
                invariant
                    k >= -1,
                    k < num_str_len as int,
                    num_str_vec@.view().subsequence(k+1, num_str_len as nat).reversed() == reversed_num_str_vec@.view(),
                decreases k,
            {
                reversed_num_str_vec.push(num_str_vec@.index(k as nat));
                k = k - 1;
            }

            string_seq_vec.extend_from_slice(&reversed_num_str_vec);

            proof {
                assert(string_seq_vec@ == string_sequence((i - 1) as nat).add(seq![' ']).add(number_to_char(current_i_nat)));
                assert(string_sequence(i as nat) == string_sequence((i - 1) as nat).add(seq![' '].add(number_to_char(i as nat))));
            }
            i = i + 1;
        }
    }

    string_seq_vec
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}