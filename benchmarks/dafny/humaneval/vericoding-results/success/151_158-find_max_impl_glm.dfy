// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function count_unique_chars(s: string): int {
    |set c | c in s|
}
// </vc-helpers>

// <vc-spec>
method find_max(strings : seq<string>) returns (s : string)

    requires |strings| > 0

    ensures s in strings
    ensures forall i : int :: 0 <= i < |strings| ==> |set c | c in s| >= |set c | c in strings[i]|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added invariant linking max_unique and max_index */
{
    var max_index := 0;
    var max_unique := count_unique_chars(strings[0]);
    
    var i := 1;
    while i < |strings|
        invariant 0 <= max_index < |strings|
        invariant 0 <= i <= |strings|
        invariant max_unique == count_unique_chars(strings[max_index])
        invariant forall j : int :: 0 <= j < i ==> count_unique_chars(strings[max_index]) >= count_unique_chars(strings[j])
    {
        var current_unique := count_unique_chars(strings[i]);
        if current_unique > max_unique {
            max_unique := current_unique;
            max_index := i;
        }
        i := i + 1;
    }
    
    s := strings[max_index];
}
// </vc-code>
