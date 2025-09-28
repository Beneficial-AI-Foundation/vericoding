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
/* helper modified by LLM (iteration 4): fixed postcondition to handle equality case correctly */
function max_strength_index(extensions: seq<string>): int
    requires |extensions| > 0
    ensures 0 <= max_strength_index(extensions) < |extensions|
    ensures forall j :: 0 <= j < |extensions| ==> strength(extensions[max_strength_index(extensions)]) >= strength(extensions[j])
    ensures forall j :: 0 <= j < max_strength_index(extensions) ==> strength(extensions[j]) < strength(extensions[max_strength_index(extensions)])
{
    if |extensions| == 1 then 0
    else
        var rest_max := max_strength_index(extensions[1..]);
        var rest_index := rest_max + 1;
        if strength(extensions[0]) > strength(extensions[rest_index]) then 0
        else if strength(extensions[0]) == strength(extensions[rest_index]) then 0
        else rest_index
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
    /* code modified by LLM (iteration 4): using helper function to find maximum strength index with strict inequality */
    var max_index := max_strength_index(extensions);
    result := class_name + "." + extensions[max_index];
}
// </vc-code>
