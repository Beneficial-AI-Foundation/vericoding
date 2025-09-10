function CountAs(s: string): int
    ensures 0 <= CountAs(s) <= |s|
    ensures CountAs(s) == |s| ==> (forall i :: 0 <= i < |s| ==> s[i] == 'a')
{
    if |s| == 0 then 0
    else if s[0] == 'a' then 1 + CountAs(s[1..])
    else CountAs(s[1..])
}

function RemoveAs(s: string): string
    ensures |RemoveAs(s)| <= |s|
    ensures |RemoveAs(s)| == |s| - CountAs(s)
    ensures forall i :: 0 <= i < |RemoveAs(s)| ==> RemoveAs(s)[i] != 'a'
{
    if |s| == 0 then ""
    else if s[0] == 'a' then RemoveAs(s[1..])
    else [s[0]] + RemoveAs(s[1..])
}

// <vc-helpers>
function CountNonAs(s: string): int
    ensures 0 <= CountNonAs(s) <= |s|
    ensures CountNonAs(s) == |s| - CountAs(s)
{
    if |s| == 0 then 0
    else if s[0] == 'a' then CountNonAs(s[1..])
    else 1 + CountNonAs(s[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(t: string) returns (result: string)
    requires |t| >= 1
    ensures result == ":(" || (|result| <= |t| && t == result + RemoveAs(result))
    ensures result != ":(" ==> (
        var z := CountAs(t);
        var nonACount := |t| - z;
        nonACount % 2 == 0 &&
        var q := nonACount / 2;
        var sLength := q + z;
        sLength <= |t| &&
        result == t[..sLength] &&
        RemoveAs(result) == t[sLength..]
    )
// </vc-spec>
// <vc-code>
{
    var z := CountAs(t);
    var nonACount := |t| - z;

    if nonACount % 2 != 0 {
        result := ":(";
        return;
    }

    var q := nonACount / 2;
    var sLength := q + z;

    if sLength > |t| {
        // This case should ideally not be reached if the problem statement implies a valid partition always exists
        // when nonACount is even and |t| >= 1.
        // It signals an edge case that might need deeper analysis or implies a condition not explicitly covered.
        result := ":(";
        return;
    }

    // Prove properties about t[..sLength] and t[sLength..]
    // We need to show that RemoveAs(t[..sLength]) == t[sLength..]
    // This implies that t[sLength..] must only consist of 'a's if t[..sLength] has processed all its non-'a's or
    // it implies properties about the structure of t that make this decomposition idempotent under RemoveAs.

    // Let's re-evaluate the postcondition: t == result + RemoveAs(result)
    // This means t[sLength..] must be exactly RemoveAs(t[..sLength]).
    // The key is that `RemoveAs(s)` effectively removes all 'a's from `s`.
    // So, `t[sLength..]` must be the result of removing all 'a's from `t[..sLength]`.
    // This is only true if `t[sLength..]` contains only non-'a' characters, and its length is `q`.
    // This seems to align perfectly with `RemoveAs(result)` producing a string of length `q` with no 'a's.
    // And `result` having `q` non-'a's and `z` 'a's, forming `sLength`.

    // The condition `t == result + RemoveAs(result)` coupled with the lengths
    // `|result| = q + z` and `|RemoveAs(result)| = q` (because `result` has `q` non-`a`s and `z` `a`s)
    // implies `|t| = (q + z) + q = 2q + z`.
    // We also know `|t| = nonACount + z`.
    // So, `2q + z = nonACount + z`, which means `2q = nonACount`. This holds by definition of `q`.

    // What needs proving is that `RemoveAs(t[..sLength]) == t[sLength..]`.
    // This comes down to proving that all 'a's in `t[..sLength]` are removed,
    // and the remaining characters form `t[sLength..]` *and* `t[sLength..]` itself
    // contains no 'a's.
    // Or, more accurately, we require `RemoveAs(t[..sLength])` to BE `t[sLength..]`.
    // This means `t[sLength..]` must *itself* be a string composed *only* of non-'a' characters,
    // and its length must be `q`.
    // And `t[..sLength]` must contain exactly `q` non-'a' characters and `z` 'a' characters.
    // This implies that `t[sLength..]` *must* contain `q` non-'a' characters and zero 'a' characters.

    // Let's verify the counts:
    // Count of Non-As in t[..sLength] must be q.
    // Count of As in t[..sLength] must be z.
    // Count of Non-As in t[sLength..] must be q.
    // Count of As in t[sLength..] must be 0.
    // So, `CountNonAs(t[..sLength]) == q` and `CountAs(t[sLength..]) == 0`.

    // This is the tricky part. The problem statement implies we *find* such an `sLength`.
    // The given `sLength = q + z` is derived from `|t| = (q + z) + q`.
    // It's not guaranteed that `t[sLength..]` will have the desired properties.

    // If the problem guarantees that such a decomposition always exists when `nonACount % 2 == 0`,
    // then the current `sLength` calculation is the only one that makes sense
    // based on the lengths `|result| = q + z` and `|RemoveAs(result)| = q`.
    // So, we would be assuming that the `t` string has the property that its suffix `t[sLength..]`
    // is exactly the `RemoveAs` of its prefix `t[..sLength]`.

    // Let's try to trace the properties.
    // `RemoveAs(s)` ensures: `forall i :: 0 <= i < |RemoveAs(s)| ==> RemoveAs(s)[i] != 'a'`
    // And `|RemoveAs(s)| == |s| - CountAs(s) == CountNonAs(s)`.

    // So for
    // `result == t[..sLength]`
    // `RemoveAs(result) == t[sLength..]`
    // We need to show:
    // 1. `CountNonAs(t[..sLength]) *or* |t[..sLength]| - CountAs(t[..sLength]) == |t[sLength..]|`
    // 2. `forall i :: 0 <= i < |t[sLength..]| ==> t[sLength..][i] != 'a'`

    // Given `sLength = q + z`:
    // `|t[..sLength]| = sLength = q + z`
    // `|t[sLength..]| = |t| - sLength = (nonACount + z) - (q + z) = nonACount - q = 2q - q = q`

    // So, from point 1, we need `CountNonAs(t[..sLength]) == q`.
    // This is equivalent to `|t[..sLength]| - CountAs(t[..sLength]) == q`.
    // `(q + z) - CountAs(t[..sLength]) == q`.
    // This implies `z - CountAs(t[..sLength]) == 0`, so `CountAs(t[..sLength]) == z`.

    // The verification condition boils down to:
    // `CountAs(t[..sLength]) == z` (number of 'a's in the prefix `result`)
    // `CountAs(t[sLength..]) == 0` (number of 'a's in the suffix `RemoveAs(result)`)

    // This is a direct consequence of the definition of `q` and `z` and the postcondition.
    // The `sLength` must exactly partition `t` such that the prefix has all `z` 'a's and `q` non-'a's,
    // and the suffix has the remaining `q` non-'a's and no 'a's.
    // This is not something we can *derive* or *prove* to be true for *any* `t` purely from `nonACount % 2 == 0`.
    // This is effectively asserting that such a decomposition `s` and `RemovAs(s)` exists for `t`.

    // The problem statement implies we compute `result` and it satisfies the postconditions.
    // The way `sLength` is derived already assumes the structure of `result` and `RemoveAs(result)`.
    // The only thing we *do* is pick `sLength` based on the counts.
    // If the input `t` does not conform to the internal structure described, then it's not possible
    // to find such a `result`.
    // The postcondition uses `forall`, so we must implement a `result` that satisfies it.
    // If it is impossible, then `result := ":("`.

    // Let's check `RemoveAs` for the required properties more deeply.
    // `RemoveAs(t[..sLength])` is guaranteed to have length `CountNonAs(t[..sLength])`.
    // And it is guaranteed to have no 'a's.
    // So, we need to ensure that `CountNonAs(t[..sLength]) == |t[sLength..]|`
    // AND `CountAs(t[sLength..]) == 0`.

    // `CountNonAs(t[..sLength]) == q` (derived earlier as needed condition)
    // `|t[sLength..]| == q` (derived earlier)
    // So, the lengths match if `CountNonAs(t[..sLength]) == q`.

    // This means we need to prove `CountAs(t[..sLength]) == z` and `CountAs(t[sLength..]) == 0`.
    // This is the core logic that the verifier assumes about the problem and how such a string `t` is formed.
    // If `t` is formed by `P + RemoveAs(P)` for some `P`, then this must hold.
    // If `t` is arbitrary, it might not hold.

    // Given the phrasing "implement a method solve", and `t` is an input, we must find if such a `result` exists.
    // If `CountAs(t[..sLength]) != z` OR `CountAs(t[sLength..]) != 0` then we must return ":(".

    // So, the final logic should be:
    result := t[..sLength];
    if CountAs(t[..sLength]) != z || CountAs(t[sLength..]) != 0 {
        result := ":(";
    }
}
// </vc-code>

