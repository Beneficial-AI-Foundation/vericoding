// <vc-preamble>

function count_upper(s: string): int
{
    if |s| == 0 then 0
    else (if 'A' <= s[0] <= 'Z' then 1 else 0) + count_upper(s[1..])
}

function count_lower(s: string): int
{
    if |s| == 0 then 0
    else (if 'a' <= s[0] <= 'z' then 1 else 0) + count_lower(s[1..])
}

function strength(s: string): int
{
    count_upper(s) - count_lower(s)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Convert lemma to non-ghost function */
function MaxStrengthIndex(s: seq<string>): (max_index: int)
    requires |s| > 0
    ensures 0 <= max_index < |s|
    ensures forall j :: 0 <= j < |s| ==> strength(s[j]) <= strength(s[max_index])
    ensures forall j :: 0 <= j < max_index ==> strength(s[j]) < strength(s[max_index])
{
    if |s| == 1 then
        0
    else
        var prev_max := MaxStrengthIndex(s[0..|s|-1]);
        if strength(s[|s|-1]) > strength(s[prev_max]) then
            |s|-1
        else
            prev_max
}
// </vc-helpers>

// <vc-spec>
method Strongest_Extension(class_name: string, extensions: seq<string>) returns (result: string)
    requires |extensions| > 0
    ensures exists i :: (0 <= i < |extensions| && result == class_name + "." + extensions[i] &&
            (forall j :: 0 <= j < |extensions| ==> strength(extensions[i]) >= strength(extensions[j])) &&
            (forall j :: 0 <= j < i ==> strength(extensions[j]) < strength(extensions[i])))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Use non-ghost function call */
    var max_index := MaxStrengthIndex(extensions);
    result := class_name + "." + extensions[max_index];
}
// </vc-code>
