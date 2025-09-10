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
    else ((s[0] as int) - ('0' as int)) * (10 * (|s|-1)) + StringToInt(s[1..])
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
            (forall i :: 0 <= i < |parts| ==> IsValidInteger(parts[i]))
    )
}

function ParseIntegerArray(s: string): seq<int>
    requires IsValidIntegerArray(s)
{
    if s == "" then []
    else var parts := Split(s, ' ');
         (seq<int> i :: 0 <= i < |parts| && IsValidInteger(parts[i]) ==> StringToInt(parts[i]))
}

// Helper to split a string into lines
function SplitLines(s: string): seq<string> 
    ensures forall i :: 0 <= i < |return| ==> !return[i].Contains('\n')
    ensures (s=="" && |return|==0) || (s!="" && |return|>0 && s == (return[0] + if |return|>1 then return[1..].Reduce((x, y) => "\n" + y) + "\n" else if s[|s|-1]=='\n' then "\n" else "" ))
{
    if s == "" then []
    else
        var lines := [];
        var start := 0;
        var i := 0;
        while i < |s|
            decreases |s| - i
            invariant 0 <= start <= i <= |s|
            invariant forall l_idx :: 0 <= l_idx < |lines| ==> !lines[l_idx].Contains('\n')
        {
            if s[i] == '\n' {
                lines := lines + [s[start..i]];
                start := i + 1;
            }
            i := i + 1;
        }
        if start < |s| { // Handle last line if not newline terminated
            lines := lines + [s[start..i]];
        } else if start == |s| && i == |s| && |lines| == 0 { // special case a single line, possibly empty, not ending with newline
            lines := lines + [""];
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
            invariant 0 <= start <= i <= |s|
            invariant forall p_idx :: 0 <= p_idx < |parts| ==> !parts[p_idx].Contains(separator)
        {
            if s[i] == separator {
                parts := parts + [s[start..i]];
                start := i + 1;
            }
            i := i + 1;
        }
        if start <= |s| { // Handle the last part
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
{
    if s == "" {
        assert MultisetFromSeq(s.seq) == map[];
        assert m == map[];
    } else {
        var s_head := s[0];
        var s_tail := s[1..];
        CharacterCountsMatchMultiset(s_tail, m[s_head := m.get(s_head, 0) - 1]);
    }
}

lemma MultisetFromSeqUpdate(s: string, idx: int, c: char)
    requires 0 <= idx < |s|
    requires 'a' <= c <= 'z'
    requires 'a' <= s[idx] <= 'z'
    ensures MultisetFromSeq(UpdateChar(s, idx, c).seq) == MultisetFromSeq(s.seq)[c := MultisetFromSeq(s.seq).get(c,0)+1][s[idx] := MultisetFromSeq(s.seq).get(s[idx],0)-1]
{
    var s_prime := UpdateChar(s, idx, c);
    var original_chars_multiset := MultisetFromSeq(s.seq);
    var s_prime_chars_multiset := MultisetFromSeq(s_prime.seq);
    assert s_prime_chars_multiset == original_chars_multiset[c := original_chars_multiset.get(c,0)+1][s[idx] := original_chars_multiset.get(s[idx],0)-1];
}

// These are for proving properties about counts of characters
lemma {:induction L} char_count_update_equal(s: string, idx: int, new_c: char, target_c: char)
    requires 0 <= idx < |s|
    ensures CountChar(UpdateChar(s, idx, new_c), target_c) == (if new_c == target_c then CountChar(s, target_c) + 1 else CountChar(s, target_c)) - (if s[idx] == target_c then 1 else 0)
{
    if |s| == 1 {
        assert s[0] == s[idx];
        assert UpdateChar(s, idx, new_c) == CharToString(new_c);
    } else if idx == 0 {
        var s_prime := s[1..];
        var s_updated_prime := UpdateChar(s, 0, new_c)[1..];
        assert s_updated_prime == s_prime;
    } else {
        var s_0 := s[0];
        var s_rest := s[1..];
        var s_updated := UpdateChar(s, idx, new_c);
        var s_updated_0 := s_updated[0];
        var s_updated_rest := s_updated[1..];
        assert s_0 == s_updated_0;
        
        char_count_update_equal(s_rest, idx - 1, new_c, target_c);
    }
}

lemma lemma_multiset_eq_after_update(original_multiset: Multiset<char>, prev_available_chars: Multiset<char>, prev_cur_t_str: string, chosen_char: char, j_target: int, m: int)
    requires 0 <= j_target < m
    requires |prev_cur_t_str| == m
    requires 'a' <= prev_cur_t_str[j_target] <= 'z'
    // This is the invariant we want to maintain, expressed before the update
    requires forall c :: 'a' <= c <= 'z' ==> prev_available_chars.get(c,0) + MultisetFromSeq(prev_cur_t_str.seq).get(c,0) == original_multiset.get(c,0)

    requires chosen_char in prev_available_chars.Keys
    requires prev_available_chars.get(chosen_char, 0) > 0
    requires 'a' <= chosen_char <= 'z'
    
    // var new_cur_t_str := UpdateChar(prev_cur_t_str, j_target, chosen_char);
    // var new_available_chars := prev_available_chars[chosen_char := prev_available_chars.get(chosen_char, 0) - 1][prev_cur_t_str[j_target] := prev_available_chars.get(prev_cur_t_str[j_target], 0) + 1];

    ensures forall c :: 'a' <= c <= 'z' ==> 
        (prev_available_chars[chosen_char := prev_available_chars.get(chosen_char, 0) - 1][prev_cur_t_str[j_target] := prev_available_chars.get(prev_cur_t_str[j_target], 0) + 1]).get(c,0) + MultisetFromSeq(UpdateChar(prev_cur_t_str, j_target, chosen_char).seq).get(c,0) == original_multiset.get(c,0)
{
    // Need to show that for any character `c`:
    // new_available_chars.get(c,0) + MultisetFromSeq(new_cur_t_str.seq).get(c,0) == original_multiset.get(c,0)

    // And also for the old char at j_target: MultisetFromSeq(prev_cur_t_str.seq).get(prev_cur_t_str[j_target], 0) - 1
    // And for the chosen_char: MultisetFromSeq(prev_cur_t_str.seq).get(chosen_char, 0) + 1

    var current_placed_multiset := MultisetFromSeq(prev_cur_t_str.seq);
    var next_placed_multiset := MultisetFromSeq(UpdateChar(prev_cur_t_str, j_target, chosen_char).seq);
    var new_available_chars := prev_available_chars[chosen_char := prev_available_chars.get(chosen_char, 0) - 1][prev_cur_t_str[j_target] := prev_available_chars.get(prev_cur_t_str[j_target], 0) + 1];


    assert next_placed_multiset == current_placed_multiset[chosen_char := current_placed_multiset.get(chosen_char,0) + 1][prev_cur_t_str[j_target] := current_placed_multiset.get(prev_cur_t_str[j_target],0) - 1];

    forall c | 'a' <= c <= 'z'
        ensures new_available_chars.get(c,0) + next_placed_multiset.get(c,0) == original_multiset.get(c,0)
    {
        var lhs := new_available_chars.get(c,0) + next_placed_multiset.get(c,0);
        var rhs := original_multiset.get(c,0);

        if c == chosen_char && c == prev_cur_t_str[j_target] {
            // Char is both chosen and replaced char (e.g., replace 'a' with 'a')
            // new_available_chars.get(c,0) = prev_available_chars.get(c,0) - 1 + 1 = prev_available_chars.get(c,0)
            // next_placed_multiset.get(c,0) = current_placed_multiset.get(c,0) + 1 - 1 = current_placed_multiset.get(c,0)
            assert lhs == prev_available_chars.get(c,0) + current_placed_multiset.get(c,0);
        } else if c == chosen_char {
            // Char is chosen_char but not the char being replaced
            // new_available_chars.get(c,0) = prev_available_chars.get(c,0) - 1
            // next_placed_multiset.get(c,0) = current_placed_multiset.get(c,0) + 1
            assert lhs == (prev_available_chars.get(c,0) - 1) + (current_placed_multiset.get(c,0) + 1);
            assert lhs == prev_available_chars.get(c,0) + current_placed_multiset.get(c,0);
        } else if c == prev_cur_t_str[j_target] {
            // Char is the one being replaced but not the chosen_char
            // new_available_chars.get(c,0) = prev_available_chars.get(c,0) + 1
            // next_placed_multiset.get(c,0) = current_placed_multiset.get(c,0) - 1
            assert lhs == (prev_available_chars.get(c,0) + 1) + (current_placed_multiset.get(c,0) - 1);
            assert lhs == prev_available_chars.get(c,0) + current_placed_multiset.get(c,0);
        } else {
            // Char `c` is not involved in this update
            // new_available_chars.get(c,0) = prev_available_chars.get(c,0)
            // next_placed_multiset.get(c,0) = current_placed_multiset.get(c,0)
            assert lhs == prev_available_chars.get(c,0) + current_placed_multiset.get(c,0);
        }
        assert lhs == rhs;
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
        var s_original_multiset := MultisetFromSeq(s_original.seq);
        
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
            invariant (forall k_char_idx :: 0 <= k_char_idx < j_target ==> 'a' <= cur_t_str[k_char_idx] <= 'z')
            invariant (forall k_char_idx :: j_target <= k_char_idx < m ==> cur_t_str[k_char_idx] == 'a')
            invariant (forall c :: 'a' <= c <= 'z' ==> available_chars.get(c,0) + MultisetFromSeq(cur_t_str.seq).get(c,0) == s_original_multiset.get(c,0))
            // The previously placed characters (at indices < j_target) satisfy the B constraints
            invariant (forall k_c :: 0 <= k_c < j_target ==> b[k_c] == SumDistancesToGreaterChars(cur_t_str, k_c))
        {
            var best_char := 'a';
            var min_cost := 1226 * m; // Larger than max possible B_j (1225 * m)

            var prev_cur_t_str_char_at_j_target := cur_t_str[j_target]; // Capture this before it's updated in the inner loop

            for c_val := 'a' as int to 'z' as int
                invariant 'a' <= best_char <= 'z'
                invariant min_cost >= 0
                invariant (forall cl :: 'a' <= cl as char <= 'z' ==>
                    ('a' <= cl as char && cl as char < (c_val as char)) ==>
                    (available_chars.get(cl as char, 0) == 0 ||
                    (var temp_t_str_candidate := UpdateChar(cur_t_str, j_target, cl as char);
                    (AbsDiff(SumDistancesToGreaterChars(temp_t_str_candidate, j_target), b[j_target]) > min_cost) ||
                    (AbsDiff(SumDistancesToGreaterChars(temp_t_str_candidate, j_target), b[j_target]) == min_cost && cl as char >= best_char))))
            {
                var c := c_val as char;
                if available_chars.get(c, 0) > 0 {
                    var temp_t_str := UpdateChar(cur_t_str, j_target, c);
                    
                    var current_abs_diff := AbsDiff(SumDistancesToGreaterChars(temp_t_str, j_target), b[j_target]);
                    if current_abs_diff < min_cost {
                        min_cost := current_abs_diff;
                        best_char := c;
                    } else if current_abs_diff == min_cost && c < best_char {
                        best_char := c;
                    }
                }
            }

            // Before update, capture current state for the lemma
            var old_cur_t_str := cur_t_str;
            var old_available_chars := available_chars;
            
            lemma_multiset_eq_after_update(s_original_multiset, old_available_chars, old_cur_t_str, best_char, j_target, m);
            
            var new_cur_t_str := UpdateChar(cur_t_str, j_target, best_char);
            cur_t_str := new_cur_t_str;
            
            // Adjust available_chars by decrementing best_char and incrementing the char that was at j_target previously (which is 'a')
            available_chars := available_chars[best_char := available_chars.get(best_char, 0) - 1][prev_cur_t_str_char_at_j_target := available_chars.get(prev_cur_t_str_char_at_j_target, 0) + 1];

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
// </vc-code>

