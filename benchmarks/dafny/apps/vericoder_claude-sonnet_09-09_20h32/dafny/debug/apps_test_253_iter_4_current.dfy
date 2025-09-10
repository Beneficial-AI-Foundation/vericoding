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
function sortThree(x: int, y: int, z: int): (int, int, int)
    requires x > 0 && y > 0 && z > 0
    ensures var (a, b, c) := sortThree(x, y, z); a <= b <= c
    ensures var (a, b, c) := sortThree(x, y, z); multiset{a, b, c} == multiset{x, y, z}
{
    if x <= y <= z then (x, y, z)
    else if x <= z <= y then (x, z, y)
    else if y <= x <= z then (y, x, z)
    else if y <= z <= x then (y, z, x)
    else if z <= x <= y then (z, x, y)
    else (z, y, x)
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
    var x := nums[0];
    var y := nums[1];
    var z := nums[2];
    
    var sorted := sortThree(x, y, z);
    var a := sorted.0;
    var b := sorted.1;
    var c := sorted.2;

    if a > 3 {
        result := "NO";
    } else if a == 3 {
        if b > 3 {
            result := "NO";
        } else if b == 3 {
            if c > 3 {
                result := "NO";
            } else {
                result := "YES";
            }
        } else {
            result := "NO";
        }
    } else if a == 1 {
        result := "YES";
    } else { // a == 2
        if b == 2 {
            result := "YES";
        } else if b > 4 {
            result := "NO";
        } else if b == 4 {
            if c == 4 {
                result := "YES";
            } else {
                result := "NO";
            }
        } else {
            result := "NO";
        }
    }
}
// </vc-code>

