// <vc-preamble>
predicate ValidInput(n: int, s1: string, s2: string)
{
    n >= 1 && |s1| == n && |s2| == n &&
    (forall i :: 0 <= i < n ==> (s1[i] == '?' || ('0' <= s1[i] <= '9'))) &&
    (forall i :: 0 <= i < n ==> (s2[i] == '?' || ('0' <= s2[i] <= '9')))
}

function compute_non_comparable_ways(n: int, s1: string, s2: string): int
    requires ValidInput(n, s1, s2)
    ensures 0 <= compute_non_comparable_ways(n, s1, s2) < 1000000007
{
    var MOD := 1000000007;
    var b1 := has_existing_s1_less_s2(s1, s2);
    var b2 := has_existing_s1_greater_s2(s1, s2);
    var total_question_marks := count_question_marks(s1) + count_question_marks(s2);
    var total_ways := power_mod(10, total_question_marks, MOD);
    var ans1 := ways_s1_leq_s2(s1, s2, MOD);
    var ans2 := ways_s1_geq_s2(s1, s2, MOD);  
    var ans3 := ways_s1_eq_s2(s1, s2, MOD);
    var subtract1 := if b2 then 0 else ans1;
    var subtract2 := if b1 then 0 else ans2;
    var add_back := if b1 || b2 then 0 else ans3;
    (total_ways - subtract1 - subtract2 + add_back + 2 * MOD) % MOD
}
// </vc-preamble>

// <vc-helpers>
function ways_s1_leq_s2(s1: string, s2: string, MOD: int): int
    requires |s1| == |s2| && MOD > 0
    requires forall i :: 0 <= i < |s1| ==> (s1[i] == '?' || ('0' <= s1[i] <= '9'))
    requires forall i :: 0 <= i < |s2| ==> (s2[i] == '?' || ('0' <= s2[i] <= '9'))
    ensures 0 <= ways_s1_leq_s2(s1, s2, MOD) < MOD
{
    ways_s1_leq_s2_helper(s1, s2, MOD, 0)
}

function ways_s1_leq_s2_helper(s1: string, s2: string, MOD: int, pos: int): int
    requires |s1| == |s2| && MOD > 0 && 0 <= pos <= |s1|
    requires forall i :: 0 <= i < |s1| ==> (s1[i] == '?' || ('0' <= s1[i] <= '9'))
    requires forall i :: 0 <= i < |s2| ==> (s2[i] == '?' || ('0' <= s2[i] <= '9'))
    ensures 0 <= ways_s1_leq_s2_helper(s1, s2, MOD, pos) < MOD
    decreases |s1| - pos
{
    if pos == |s1| then 1 % MOD
    else
        var current_ways := 
            if s1[pos] == '?' && s2[pos] == '?' then 55
            else if s1[pos] == '?' then 
                var digit2 := (s2[pos] as int) - ('0' as int);
                digit2 + 1
            else if s2[pos] == '?' then
                var digit1 := (s1[pos] as int) - ('0' as int);
                10 - digit1
            else 1;
        var rest := ways_s1_leq_s2_helper(s1, s2, MOD, pos + 1);
        (current_ways * rest) % MOD
}

function ways_s1_geq_s2(s1: string, s2: string, MOD: int): int
    requires |s1| == |s2| && MOD > 0
    requires forall i :: 0 <= i < |s1| ==> (s1[i] == '?' || ('0' <= s1[i] <= '9'))
    requires forall i :: 0 <= i < |s2| ==> (s2[i] == '?' || ('0' <= s2[i] <= '9'))
    ensures 0 <= ways_s1_geq_s2(s1, s2, MOD) < MOD
{
    ways_s1_geq_s2_helper(s1, s2, MOD, 0)
}

function ways_s1_geq_s2_helper(s1: string, s2: string, MOD: int, pos: int): int
    requires |s1| == |s2| && MOD > 0 && 0 <= pos <= |s1|
    requires forall i :: 0 <= i < |s1| ==> (s1[i] == '?' || ('0' <= s1[i] <= '9'))
    requires forall i :: 0 <= i < |s2| ==> (s2[i] == '?' || ('0' <= s2[i] <= '9'))
    ensures 0 <= ways_s1_geq_s2_helper(s1, s2, MOD, pos) < MOD
    decreases |s1| - pos
{
    if pos == |s1| then 1 % MOD
    else
        var current_ways := 
            if s1[pos] == '?' && s2[pos] == '?' then 55
            else if s1[pos] == '?' then 
                var digit2 := (s2[pos] as int) - ('0' as int);
                10 - digit2
            else if s2[pos] == '?' then
                var digit1 := (s1[pos] as int) - ('0' as int);
                digit1 + 1
            else 1;
        var rest := ways_s1_geq_s2_helper(s1, s2, MOD, pos + 1);
        (current_ways * rest) % MOD
}

function ways_s1_eq_s2(s1: string, s2: string, MOD: int): int
    requires |s1| == |s2| && MOD > 0
    requires forall i :: 0 <= i < |s1| ==> (s1[i] == '?' || ('0' <= s1[i] <= '9'))
    requires forall i :: 0 <= i < |s2| ==> (s2[i] == '?' || ('0' <= s2[i] <= '9'))
    ensures 0 <= ways_s1_eq_s2(s1, s2, MOD) < MOD
{
    ways_s1_eq_s2_helper(s1, s2, MOD, 0)
}

function ways_s1_eq_s2_helper(s1: string, s2: string, MOD: int, pos: int): int
    requires |s1| == |s2| && MOD > 0 && 0 <= pos <= |s1|
    requires forall i :: 0 <= i < |s1| ==> (s1[i] == '?' || ('0' <= s1[i] <= '9'))
    requires forall i :: 0 <= i < |s2| ==> (s2[i] == '?' || ('0' <= s2[i] <= '9'))
    ensures 0 <= ways_s1_eq_s2_helper(s1, s2, MOD, pos) < MOD
    decreases |s1| - pos
{
    if pos == |s1| then 1 % MOD
    else
        var current_ways := 
            if s1[pos] == '?' && s2[pos] == '?' then 10
            else if s1[pos] == '?' || s2[pos] == '?' then 1
            else 1;
        var rest := ways_s1_eq_s2_helper(s1, s2, MOD, pos + 1);
        (current_ways * rest) % MOD
}

function has_existing_s1_less_s2(s1: string, s2: string): bool
    requires |s1| == |s2|
    requires forall i :: 0 <= i < |s1| ==> (s1[i] == '?' || ('0' <= s1[i] <= '9'))
    requires forall i :: 0 <= i < |s2| ==> (s2[i] == '?' || ('0' <= s2[i] <= '9'))
{
    exists i :: 0 <= i < |s1| && s1[i] != '?' && s2[i] != '?' && s1[i] < s2[i]
}

function has_existing_s1_greater_s2(s1: string, s2: string): bool
    requires |s1| == |s2|
    requires forall i :: 0 <= i < |s1| ==> (s1[i] == '?' || ('0' <= s1[i] <= '9'))
    requires forall i :: 0 <= i < |s2| ==> (s2[i] == '?' || ('0' <= s2[i] <= '9'))
{
    exists i :: 0 <= i < |s1| && s1[i] != '?' && s2[i] != '?' && s1[i] > s2[i]
}

function count_question_marks(s: string): int
    ensures count_question_marks(s) >= 0
{
    |set i | 0 <= i < |s| && s[i] == '?'|
}

function power_mod(base: int, exp: int, mod: int): int
    requires base >= 0 && exp >= 0 && mod > 0
    ensures 0 <= power_mod(base, exp, mod) < mod
{
    if exp == 0 then 1 % mod
    else if exp == 1 then base % mod
    else
        var half := power_mod(base, exp / 2, mod);
        if exp % 2 == 0 then (half * half) % mod
        else (((half * half) % mod) * base) % mod
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s1: string, s2: string) returns (result: int)
    requires ValidInput(n, s1, s2)
    ensures 0 <= result < 1000000007
    ensures result == compute_non_comparable_ways(n, s1, s2)
// </vc-spec>
// <vc-code>
{
    var MOD := 1000000007;
    var b1 := has_existing_s1_less_s2(s1, s2);
    var b2 := has_existing_s1_greater_s2(s1, s2);
    var total_question_marks := count_question_marks(s1) + count_question_marks(s2);
    var total_ways := power_mod(10, total_question_marks, MOD);
    var ans1 := ways_s1_leq_s2(s1, s2, MOD);
    var ans2 := ways_s1_geq_s2(s1, s2, MOD);  
    var ans3 := ways_s1_eq_s2(s1, s2, MOD);
    var subtract1 := if b2 then 0 else ans1;
    var subtract2 := if b1 then 0 else ans2;
    var add_back := if b1 || b2 then 0 else ans3;
    result := (total_ways - subtract1 - subtract2 + add_back + 2 * MOD) % MOD;
}
// </vc-code>
