predicate ValidInputFormat(input: string)
{
    |input| > 0 && 
    exists lines: seq<string> ::
        lines == SplitLines(input) &&
        |lines| >= 1 &&
        IsValidInteger(lines[0]) &&
        var t := StringToInt(lines[0]);
        1 <= t <= 100 &&
        |lines| >= 1 + 3*t &&
        forall i :: 0 <= i < t ==> 
            var base_idx := 1 + 3*i;
            base_idx + 2 < |lines| &&
            IsValidString(lines[base_idx]) &&
            IsValidInteger(lines[base_idx + 1]) &&
            IsValidIntegerArray(lines[base_idx + 2]) &&
            var s := lines[base_idx];
            var m := StringToInt(lines[base_idx + 1]);
            var b_array := ParseIntegerArray(lines[base_idx + 2]);
            1 <= |s| <= 50 &&
            (forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z') &&
            1 <= m <= |s| &&
            |b_array| == m &&
            forall k :: 0 <= k < m ==> 0 <= b_array[k] <= 1225
}

predicate ValidOutputFormat(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    |test_cases| > 0 ==> 
    exists output_lines: seq<string> ::
        output_lines == SplitLines(output) &&
        |output_lines| >= |test_cases| &&
        forall i :: 0 <= i < |test_cases| ==> 
            var (s, m, b) := test_cases[i];
            i < |output_lines| &&
            |output_lines[i]| == m &&
            forall j :: 0 <= j < |output_lines[i]| ==> 'a' <= output_lines[i][j] <= 'z'
}

predicate OutputSatisfiesConstraints(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    var output_lines := SplitLines(output);
    |test_cases| > 0 && |output_lines| >= |test_cases| ==>
    forall i :: 0 <= i < |test_cases| ==> 
        var (s, m, b) := test_cases[i];
        i < |output_lines| &&
        var t := output_lines[i];
        |t| == m &&
        (forall j :: 0 <= j < m ==> 
            b[j] == SumDistancesToGreaterChars(t, j))
}

predicate PreservesCharacterUsage(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    var output_lines := SplitLines(output);
    |test_cases| > 0 && |output_lines| >= |test_cases| ==>
    forall i :: 0 <= i < |test_cases| ==> 
        var (s, m, b) := test_cases[i];
        i < |output_lines| &&
        var t := output_lines[i];
        forall c :: 'a' <= c <= 'z' ==> CountChar(t, c) <= CountChar(s, c)
}

predicate ContainsNewlineTerminatedResults(output: string)
{
    |output| > 0 ==> output[|output|-1] == '\n'
}

function SumDistancesToGreaterChars(t: string, j: int): int
    requires 0 <= j < |t|
{
    SumDistancesToGreaterCharsHelper(t, j, 0)
}

function AbsDiff(i: int, j: int): int
    ensures AbsDiff(i, j) >= 0
    ensures AbsDiff(i, j) == if i >= j then i - j else j - i
{
    if i >= j then i - j else j - i
}

// <vc-helpers>
predicate IsValidInteger(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function StringToInt(s: string): int
    requires IsValidInteger(s)
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else ((s[0] as int) - ('0' as int)) * (10 power (|s|-1)) + StringToInt(s[1..])
}

predicate IsValidString(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z')
}

predicate IsValidIntegerArray(s: string)
{
    s == "" || (
        exists parts: seq<string> ::
            parts == Split(s, ' ') &&
            |parts| > 0 &&
            forall i :: 0 <= i < |parts| ==> IsValidInteger(parts[i])
    )
}

function ParseIntegerArray(s: string): seq<int>
    requires IsValidIntegerArray(s)
{
    if s == "" then []
    else var parts := Split(s, ' ');
         if |parts| == 0 then [] else (forall i :: 0 <= i < |parts| :: StringToInt(parts[i]))
}

// Helper to split a string into lines
function SplitLines(s: string): seq<string> 
    ensures forall i :: 0 <= i < |return| ==> !return[i].Contains('\n')
    ensures (s=="" && |return|==0) || (s!="" && |return|>0 && s == (return[0] + if |return|>1 then return[1..].Reduce((x, y) => "\n" + y) else "" ))
{
    if s == "" then []
    else
        var lines := [];
        var start := 0;
        var i := 0;
        while i < |s|
            decreases |s| - i
        {
            if s[i] == '\n' {
                lines := lines + [s[start..i]];
                start := i + 1;
            }
            i := i + 1;
        }
        if start < |s| || (start == |s| && i == |s|) { // Handle last line or empty string with newline
            lines := lines + [s[start..i]];
        }
        lines
}

function Split(s: string, separator: char): seq<string>
    ensures forall i :: 0 <= i < |return| ==> !return[i].Contains(separator)
{
    if s == "" then []
    else
        var parts := [];
        var start := 0;
        var i := 0;
        while i < |s|
            decreases |s| - i
        {
            if s[i] == separator {
                parts := parts + [s[start..i]];
                start := i + 1;
            }
            i := i + 1;
        }
        if start <= |s| {
            parts := parts + [s[start..i]];
        }
        parts
}

function GetTestCases(input: string): seq<(char seq, int, seq<int>)>
    requires ValidInputFormat(input)
{
    var lines := SplitLines(input);
    var t := StringToInt(lines[0]);
    var test_cases: seq<(char seq, int, seq<int>)> := [];
    var i := 0;
    while i < t
        decreases t - i
        invariant 0 <= i <= t
        invariant |test_cases| == i
        invariant forall k :: 0 <= k < i ==> 
            var base_idx_k := 1 + 3*k;
            var s_k := lines[base_idx_k];
            var m_k := StringToInt(lines[base_idx_k + 1]);
            var b_array_k := ParseIntegerArray(lines[base_idx_k + 2]);
            var (s_tc_k, m_tc_k, b_tc_k) := test_cases[k];
            s_tc_k == s_k.seq && m_tc_k == m_k && b_tc_k == b_array_k
    {
        var base_idx := 1 + 3*i;
        var s := lines[base_idx];
        var m := StringToInt(lines[base_idx + 1]);
        var b_array := ParseIntegerArray(lines[base_idx + 2]);
        test_cases := test_cases + [(s.seq, m, b_array)];
        i := i + 1;
    }
    test_cases
}

function SumDistancesToGreaterCharsHelper(t: string, j: int, k: int): int
    requires 0 <= j < |t|
    requires 0 <= k <= |t|
    decreases |t| - k
    ensures SumDistancesToGreaterCharsHelper(t, j, k) >= 0
{
    if k == |t| then 0
    else
        var current_sum := SumDistancesToGreaterCharsHelper(t, j, k+1);
        if t[k] > t[j] then current_sum + AbsDiff(j, k)
        else current_sum
}

function CountChar(s: string, c: char): int
    requires 'a' <= c <= 'z'
    ensures 0 <= CountChar(s, c) <= |s|
{
    if s == "" then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function CharToString(c: char): string {
  "" + c
}
function UpdateChar(s: string, idx: int, c: char): string
    requires 0 <= idx < |s|
    ensures |return| == |s|
    ensures forall i :: 0 <= i < |s| ==> (i == idx ==> return[i] == c) && (i != idx ==> return[i] == s[i])
{
    s[..idx] + CharToString(c) + s[idx+1..]
}

type Multiset<+T> = map<T, nat>

function MultisetFromSeq<T>(s: seq<T>): Multiset<T> {
    var m: Multiset<T> := map[];
    for x in s {
        m := m[x := m.get(x, 0) + 1];
    }
    return m
}

predicate SubMultiset<T>(A: Multiset<T>, B: Multiset<T>) {
    forall t :: A.get(t, 0) <= B.get(t, 0)
}

lemma SumDistancesToGreaterChars_monotonic(t: string, j: int, k: int, val: int)
    requires 0 <= j < |t|
    requires 0 <= k <= |t|
    requires SumDistancesToGreaterCharsHelper(t, j, k) == val
    ensures SumDistancesToGreaterCharsHelper(t, j, k) == val
{}

lemma SumDistancesToGreaterChars_nonnegative(t: string, j: int)
    requires 0 <= j < |t|
    ensures SumDistancesToGreaterChars(t, j) >= 0
{
    SumDistancesToGreaterCharsHelper_nonnegative_lemma(t, j, 0);
}

lemma SumDistancesToGreaterCharsHelper_nonnegative_lemma(t: string, j: int, k: int)
    requires 0 <= j < |t|
    requires 0 <= k <= |t|
    ensures SumDistancesToGreaterCharsHelper(t, j, k) >= 0
    decreases |t| - k
{
    if k < |t| {
        SumDistancesToGreaterCharsHelper_nonnegative_lemma(t, j, k+1);
    }
}

lemma CharacterCountsMatchMultiset(s: string, m: Multiset<char>)
    requires forall c :: 'a' <= c <= 'z' ==> CountChar(s, c) == m.get(c, 0)
    ensures MultisetFromSeq(s.seq) == m
{}

lemma MultisetFromSeqUpdate(s: string, idx: int, c: char)
    requires 0 <= idx < |s|
    requires 'a' <= c <= 'z'
    requires 'a' <= s[idx] <= 'z'
    ensures MultisetFromSeq(UpdateChar(s, idx, c).seq) == MultisetFromSeq(s.seq)[c := MultisetFromSeq(s.seq).get(c,0)+1][s[idx] := MultisetFromSeq(s.seq).get(s[idx],0)-1]
{
    var s_prime := UpdateChar(s, idx, c);
    var original_chars := MultisetFromSeq(s.seq);
    var s_prime_chars := MultisetFromSeq(s_prime.seq);
    assert s_prime_chars == original_chars[c := original_chars.get(c,0)+1][s[idx] := original_chars.get(s[idx],0)-1];
}

// These are for proving properties about counts of characters
lemma {:induction L} char_count_update_equal(s: string, idx: int, new_c: char, target_c: char)
    requires 0 <= idx < |s|
    ensures CountChar(UpdateChar(s, idx, new_c), target_c) == (if new_c == target_c then CountChar(s, target_c) + 1 else CountChar(s, target_c)) - (if s[idx] == target_c then 1 else 0)
{
    if |s| == 1 {
        assert s[0] == s[idx];
        assert UpdateChar(s, idx, new_c) == CharToString(new_c);
        if new_c == target_c {
            assert CountChar(new_c, target_c) == 1;
            assert (if s[idx] == target_c then 1 else 0) == (if s[0] == target_c then 1 else 0);
            assert (CountChar(s, target_c) + 1) - (if s[0] == target_c then 1 else 0) == (if s[0] == target_c then 1 else 0) + 1 - (if s[0] == target_c then 1 else 0) == 1;
        } else {
            assert CountChar(new_c, target_c) == 0;
            assert CountChar(s, target_c) - (if s[0] == target_c then 1 else 0) == (if s[0] == target_c then 1 else 0) - (if s[0] == target_c then 1 else 0) == 0;
        }
    } else if idx == 0 {
        var s_prime := s[1..];
        var s_updated_prime := UpdateChar(s, 0, new_c)[1..];
        assert s_updated_prime == s_prime;
        var term_new_c := if new_c == target_c then 1 else 0;
        var term_s_0 := if s[0] == target_c then 1 else 0;

        assert CountChar(UpdateChar(s, 0, new_c), target_c) == term_new_c + CountChar(s_updated_prime, target_c);
        assert CountChar(s, target_c) == term_s_0 + CountChar(s_prime, target_c);

        assert CountChar(s_updated_prime, target_c) == CountChar(s_prime, target_c);

        assert term_new_c + CountChar(s_prime, target_c) == (term_new_c - term_s_0) + term_s_0 + CountChar(s_prime, target_c);
        assert CountChar(UpdateChar(s, 0, new_c), target_c) == (term_new_c - term_s_0) + CountChar(s, target_c);
        assert (if new_c == target_c then CountChar(s, target_c) + 1 else CountChar(s, target_c)) - (if s[idx] == target_c then 1 else 0) ==
               (if new_c == target_c then CountChar(s, target_c) + 1 else CountChar(s, target_c)) - (if s[0] == target_c then 1 else 0);
    } else {
        var s_0 := s[0];
        var s_rest := s[1..];
        var s_updated := UpdateChar(s, idx, new_c);
        var s_updated_0 := s_updated[0];
        var s_updated_rest := s_updated[1..];
        assert s_0 == s_updated_0;
        
        char_count_update_equal(s_rest, idx - 1, new_c, target_c);

        if s_0 == target_c {
            assert CountChar(s, target_c) == 1 + CountChar(s_rest, target_c);
            assert CountChar(s_updated, target_c) == 1 + CountChar(s_updated_rest, target_c);
            assert CountChar(s_updated_rest, target_c) == (if new_c == target_c then CountChar(s_rest, target_c) + 1 else CountChar(s_rest, target_c)) - (if s_rest[idx-1] == target_c then 1 else 0);
            assert CountChar(s_updated, target_c) == 1 + ( (if new_c == target_c then CountChar(s_rest, target_c) + 1 else CountChar(s_rest, target_c)) - (if s_rest[idx-1] == target_c then 1 else 0) );

        } else {
            assert CountChar(s, target_c) == CountChar(s_rest, target_c);
            assert CountChar(s_updated, target_c) == CountChar(s_updated_rest, target_c);
             assert CountChar(s_updated_rest, target_c) == (if new_c == target_c then CountChar(s_rest, target_c) + 1 else CountChar(s_rest, target_c)) - (if s_rest[idx-1] == target_c then 1 else 0);
            assert CountChar(s_updated, target_c) == ( (if new_c == target_c then CountChar(s_rest, target_c) + 1 else CountChar(s_rest, target_c)) - (if s_rest[idx-1] == target_c then 1 else 0) );
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInputFormat(stdin_input)
    ensures ValidOutputFormat(result, stdin_input)
    ensures OutputSatisfiesConstraints(result, stdin_input)
    ensures PreservesCharacterUsage(result, stdin_input)
    ensures result != "" ==> ContainsNewlineTerminatedResults(result)
// </vc-spec>
// <vc-code>
{
    var output_lines := new seq<string>(0);
    var test_cases := GetTestCases(stdin_input);

    for i := 0 to |test_cases| - 1
        invariant 0 <= i <= |test_cases|
        invariant |output_lines| == i
        invariant forall k :: 0 <= k < i ==> 
            var (s_original_k, m_k, b_k) := test_cases[k];
            var output_k := output_lines[k];
            |output_k| == m_k &&
            (forall j_target :: 0 <= j_target < m_k ==> 
                b_k[j_target] == SumDistancesToGreaterChars(output_k, j_target)) &&
            (forall c :: 'a' <= c <= 'z' ==> CountChar(output_k, c) <= CountChar(s_original_k, c))
    {
        var (s_original, m, b) := test_cases[i];
        var s_multiset := MultisetFromSeq(s_original.seq);
        
        var cur_t := new char[m];
        
        // Initialize t with dummy chars, which will be replaced
        for k := 0 to m - 1 {
            cur_t[k] := 'a'; // Placeholder, will be overwritten
        }
        var cur_t_str := (cur_t : seq<char>) as string;

        var available_chars := MultisetFromSeq(s_original.seq);

        for j_target := 0 to m - 1
            invariant 0 <= j_target <= m
            invariant |cur_t_str| == m
            invariant (available_chars `SubMultiset` MultisetFromSeq(s_original.seq))
            invariant forall k :: 0 <= k < j_target ==> 'a' <= cur_t_str[k] <= 'z'
            invariant forall c :: 'a' <= c <= 'z' ==> available_chars.get(c,0) + CountChar(cur_t_str[0..j_target], c) == CountChar(s_original, c)
            invariant forall k_char :: 0 <= k_char < j_target ==>
                b[k_char] == SumDistancesToGreaterChars(cur_t_str, k_char)
        {
            var best_char := 'a';
            var min_cost := 1226 * m; // Larger than max possible B_j (1225 * m)

            for c_val := 'a' as int to 'z' as int
                invariant 'a' <= best_char <= 'z'
                invariant min_cost >= 0
                invariant forall cl :: 'a' <= cl < c_val as char ==>
                    available_chars.get(cl, 0) == 0 ||
                    (var temp_t_str := UpdateChar(cur_t_str, j_target, cl);
                    (available_chars.get(cl, 0) > 0 ==>
                        (SumDistancesToGreaterChars(temp_t_str, j_target) >= min_cost))
                    )
            {
                var c := c_val as char;
                if available_chars.get(c, 0) > 0 {
                    var temp_t_str_seq := new char[m];
                    for k := 0 to m-1 { temp_t_str_seq[k] := cur_t_str[k]; }
                    temp_t_str_seq[j_target] := c;
                    var temp_t_str := (temp_t_str_seq : seq<char>) as string;
                    
                    var current_sum := SumDistancesToGreaterChars(temp_t_str, j_target);
                    assert SumDistancesToGreaterChars_nonnegative(temp_t_str, j_target);
                    if AbsDiff(current_sum, b[j_target]) < min_cost {
                        min_cost := AbsDiff(current_sum, b[j_target]);
                        best_char := c;
                    } else if AbsDiff(current_sum, b[j_target]) == min_cost && c < best_char {
                        best_char := c;
                    }
                }
            }

            var old_char_at_j_target := cur_t_str[j_target];
            if available_chars.get(best_char, 0) > 0 {
                // Adjust counts for characters moving in and out of the position
                // The character at j_target should be `null` in `available_chars` if it was selected
                // But it's not removed from available_chars here, it's just what we choose.
                // The available_chars is about the multiset from s_original MINUS already placed chars.

                // Remove the `old_char_at_j_target` count IF it was already a valid char
                // But it's always 'a' initially, so we don't 'add it back' as it was never taken out.
                // We are only setting this position. The `available_chars` represents the remaining char counts.
                // The initial `cur_t_str` starts with 'a' chars. These 'a' chars are not taken from `available_chars`.
                // `available_chars` reflects the count of characters from `s_original` that HAVE NOT BEEN USED to fill `cur_t_str` at indices < j_target.

                // When we `UpdateChar`, we are conceptually "taking" a character `best_char` from `available_chars`
                // and if `cur_t_str[j_target]` (which is 'a') was from `s_original` and still considered "available",
                // then that 'a' would be put back. But here, `cur_t_str[j_target]` is a placeholder.
                // Thus, we just decrement `best_char` in `available_chars`.

                var new_cur_t_str := UpdateChar(cur_t_str, j_target, best_char);
                cur_t_str := new_cur_t_str;
                
                available_chars := available_chars[best_char := available_chars.get(best_char, 0) - 1];

                // Prove that MultisetFromSeq(cur_t_str[0..j_target+1]) + available_chars == MultisetFromSeq(s_original.seq)
                lemma_multiset_eq_after_update(MultisetFromSeq(s_original.seq), available_chars, MultisetFromSeq(cur_t_str[0..j_target]), best_char, j_target);
            }
        }
        output_lines := output_lines + [cur_t_str];
    }
    
    var final_output := "";
    if |output_lines| > 0 {
        final_output := output_lines[0];
        for i := 1 to |output_lines| - 1 {
            final_output := final_output + "\n" + output_lines[i];
        }
        final_output := final_output + "\n";
    }
    return final_output;
}

lemma lemma_multiset_eq_after_update(original_multiset: Multiset<char>, prev_available_chars: Multiset<char>, prev_placed_chars: Multiset<char>, chosen_char: char, j_target: int)
    requires MultisetFromSeq(original_multiset.Keys) == original_multiset // placeholder for ensuring original_multiset is from s_original
    // Invariant from loop: forall c :: 'a' <= c <= 'z' ==> prev_available_chars.get(c,0) + prev_placed_chars.get(c,0) == original_multiset.get(c,0)
    requires forall c :: 'a' <= c <= 'z' ==> prev_available_chars.get(c,0) + MultisetFromSeq(UpdateChar("a"*(j_target), j_target-1, prev_placed_chars.Keys)-1).get(c,0) == original_multiset.get(c,0)


{}
// </vc-code>

