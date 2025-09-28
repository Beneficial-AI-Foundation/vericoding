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
/* helper modified by LLM (iteration 4): The `index_of` function has been removed because it was unused and caused compilation errors within the `Strongest` predicate. The `Strongest` predicate has been simplified since its original purpose was not fully aligned with the required postconditions, and the required logic is now handled in the main method body. */
predicate Strongest(ext: string, extensions: seq<string>, class_name: string)
{
    true
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
/* code modified by LLM (iteration 4): Removed the now-unused helper function and fixed the loop invariants based on the Dafny error message. The logic for finding the strongest extension is now better aligned with the postcondition. */
{
    var strongest_extension_so_far: string := extensions[0];
    var strongest_index: int := 0;
    var i := 1;
    while i < |extensions|
        invariant 0 <= i <= |extensions|
        invariant 0 <= strongest_index < i
        invariant strongest_extension_so_far == extensions[strongest_index]
        invariant (forall j :: 0 <= j < i ==> strength(strongest_extension_so_far) >= strength(extensions[j]))
        invariant (forall j :: 0 <= j < strongest_index ==> strength(extensions[j]) < strength(strongest_extension_so_far))
    {
        if strength(extensions[i]) > strength(strongest_extension_so_far) {
            strongest_extension_so_far := extensions[i];
            strongest_index := i;
        }
        i := i + 1;
    }
    result := class_name + "." + strongest_extension_so_far;
}
// </vc-code>
