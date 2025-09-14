// <vc-preamble>
predicate IsLowerCase(c: char)
{
    c >= 'a' && c <= 'z'
}

function ShiftMinus32Spec(c: char): char
    requires IsLowerCase(c)
{
    (c as int - 32) as char
}

function InnerExprToUppercase(str1: seq<char>, i: int): char
    requires 0 <= i < |str1|
{
    if IsLowerCase(str1[i]) then
        ShiftMinus32Spec(str1[i])
    else
        str1[i]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Kept helper function and added a lemma to prove its equivalence to the spec function. */
function ToUpperChar(str: seq<char>, i: int): char
    requires 0 <= i < |str|
{
    if IsLowerCase(str[i]) then ShiftMinus32Spec(str[i]) else str[i]
}

lemma EquivalenceLemma(str: seq<char>, i: int)
  requires 0 <= i < |str|
  ensures ToUpperChar(str, i) == InnerExprToUppercase(str, i)
{
  // The bodies of ToUpperChar and InnerExprToUppercase are identical,
  // so Dafny can prove this by function expansion.
}
// </vc-helpers>

// <vc-spec>
method ToUppercase(str1: seq<char>) returns (result: seq<char>)
    ensures
        |str1| == |result| &&
        forall i :: 0 <= i < |str1| ==> result[i] == InnerExprToUppercase(str1, i)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Switched to an imperative loop to resolve precondition proof failure. */
    var i := 0;
    result := [];
    while i < |str1|
        invariant 0 <= i <= |str1|
        invariant |result| == i
        // This invariant connects the implementation back to the specification's expression
        invariant forall j :: 0 <= j < i ==> result[j] == InnerExprToUppercase(str1, j)
    {
        // The loop condition ensures 0 <= i < |str1|, satisfying preconditions.
        // Prove that our helper is equivalent to the spec's function for this index.
        EquivalenceLemma(str1, i);
        var upper_char := ToUpperChar(str1, i);
        result := result + [upper_char];
        i := i + 1;
    }
}
// </vc-code>
