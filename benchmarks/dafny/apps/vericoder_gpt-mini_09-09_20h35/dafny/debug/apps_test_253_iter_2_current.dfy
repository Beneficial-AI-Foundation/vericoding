predicate ValidInput(nums: seq<int>)
{
    |nums| == 3 &&
    forall i :: 0 <= i < |nums| ==> nums[i] > 0 &&
    forall i :: 0 <= i < |nums| ==> nums[i] <= 1500
}

function computeResult(x: int, y: int, z: int): string
    requires x > 0 && y > 0 && z > 0
    requires x <= 1500 && y <= 1500 && z <= 1500
{
    var sorted := sortThree(x, y, z);
    var a := sorted.0;
    var b := sorted.1;
    var c := sorted.2;

    if a > 3 then "NO"
    else if a == 3 then
        if b > 3 then "NO"
        else if b == 3 then
            if c > 3 then "NO" else "YES"
        else "NO"
    else if a == 1 then "YES"
    else // a == 2
        if b == 2 then "YES"
        else if b > 4 then "NO"
        else if b == 4 then
            if c == 4 then "YES" else "NO"
        else "NO"
}

// <vc-helpers>
function sortThree(x: int, y: int, z: int) : (a: int, b: int, c: int)
    ensures a <= b && b <= c
    ensures multiset([a, b, c]) == multiset([x, y, z])
{
    if x <= y && x <= z then
        if y <= z then (x, y, z) else (x, z, y)
    else if y <= x && y <= z then
        if x <= z then (y, x, z) else (y, z, x)
    else
        if x <= y then (z, x, y) else (z, y, x)
}
// </vc-helpers>

// <vc-spec>
method solve(nums: seq<int>) returns (result: string)
    requires ValidInput(nums)
    ensures result == "YES" || result == "NO"
    ensures result == computeResult(nums[0], nums[1], nums[2])
// </vc-spec>
// <vc-code>
{
  result := computeResult(nums[0], nums[1], nums[2]);
}
// </vc-code>

