

// <vc-helpers>
function substr_in_string(s: string, substr: string, i: int): bool
    requires 0 <= i <= |s| - |substr|
    ensures substr_in_string(s, substr, i) == (s[i..i+|substr|] == substr)

ghost function CountSet(s: string, substr: string): iset<int>
    ensures CountSet(s, substr) == set i | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr

lemma {:induction s, substr} CardCountSetEqualsHowMany(s: string, substr: string)
    ensures |CountSet(s, substr)| == how_many_aux(s, substr, 0)

function how_many_aux(s: string, substr: string, pos: int): int
    decreases |s| - pos
    requires 0 <= pos <= |s|
    ensures how_many_aux(s, substr, pos) == |set i | pos <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
{
    if pos > |s| - |substr| then 0
    else if substr_in_string(s, substr, pos) then
        1 + how_many_aux(s, substr, pos + 1)
    else
        how_many_aux(s, substr, pos + 1)
}
// </vc-helpers>

// <vc-spec>
method how_many_times(s: string, substr: string) returns (times: int)
    // post-condition-start
    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
    // post-condition-end
// </vc-spec>
// <vc-code>
{
    times := 0;
    var i := 0;
    while i <= |s| - |substr|
        invariant 0 <= i <= |s| - |substr| + 1
        invariant times == how_many_aux(s, substr, i)
    {
        if s[i..i+|substr|] == substr {
            times := times + 1;
        }
        i := i + 1;
    }
    assert times == how_many_aux(s, substr, 0);
}
// </vc-code>

