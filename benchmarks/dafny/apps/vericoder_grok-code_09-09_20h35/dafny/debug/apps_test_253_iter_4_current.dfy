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
predicate ValidInput(nums: seq<int>)
{
    |nums| == 3 &&
    (forall i :: 0 <= i < |nums| ==> nums[i] > 0) &&
    (forall i :: 0 <= i < |nums| ==> nums[i] <= 1500)
}

function sortThree(a: int, b: int, c: int): (int, int, int)
{
    if a <= b && b <= c then (a, b, c)
    else if a <= c && c <= b then (a, c, b)
    else if b <= a && a <= c then (b, a, c)
    else if b <= c && c <= a then (b, c, a)
    else if c <= a && a <= b then (c, a, b)
    else (c, b, a)
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

