// <vc-preamble>
predicate ValidInput(n: int, t: string)
{
    n >= 1 && |t| == n && forall i :: 0 <= i < |t| ==> t[i] == '0' || t[i] == '1'
}

function ExpectedResult(n: int, t: string): int
    requires ValidInput(n, t)
{
    if n == 1 then
        if t == "0" then 10000000000 else 20000000000
    else if n == 2 then
        if t == "00" then 0
        else if t == "01" then 9999999999
        else if t == "10" then 10000000000
        else 10000000000
    else
        var repeat_num := (n + 6) / 3;
        var ref := seq(repeat_num * 3, i => if i % 3 == 0 then '1' else if i % 3 == 1 then '1' else '0');
        var base_count := 10000000000 - repeat_num + 2;
        if |ref| >= n && ref[0..n] == t then
            base_count + (if n % 3 == 0 then 1 else 0)
        else if |ref| >= n + 1 && ref[1..n+1] == t then
            base_count
        else if |ref| >= n + 2 && ref[2..n+2] == t then
            base_count + (if n % 3 == 2 then -1 else 0)
        else
            0
}
// </vc-preamble>

// <vc-helpers>
lemma RefEquivalence(repeat_num: int, ref: string)
    requires repeat_num >= 0
    requires |ref| == repeat_num * 3
    requires forall k :: 0 <= k < repeat_num ==> k * 3 + 2 < |ref| && ref[k*3] == '1' && ref[k*3+1] == '1' && ref[k*3+2] == '0'
    ensures ref == seq(repeat_num * 3, i => if i % 3 == 0 then '1' else if i % 3 == 1 then '1' else '0')
{
    var expected := seq(repeat_num * 3, i => if i % 3 == 0 then '1' else if i % 3 == 1 then '1' else '0');
    forall i | 0 <= i < |ref|
        ensures ref[i] == expected[i]
    {
        var k := i / 3;
        var pos := i % 3;
        assert 0 <= k < repeat_num;
        assert k * 3 + 2 < |ref|;
        assert ref[k*3] == '1' && ref[k*3+1] == '1' && ref[k*3+2] == '0';
        assert i == k * 3 + pos;
        if pos == 0 {
            assert i == k * 3;
            assert ref[i] == ref[k*3] == '1';
            assert expected[i] == '1';
        } else if pos == 1 {
            assert i == k * 3 + 1;
            assert ref[i] == ref[k*3+1] == '1';
            assert expected[i] == '1';
        } else {
            assert pos == 2;
            assert i == k * 3 + 2;
            assert ref[i] == ref[k*3+2] == '0';
            assert expected[i] == '0';
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, t: string) returns (result: int)
    requires ValidInput(n, t)
    requires n <= 200000  // Based on problem constraints
    ensures result >= 0
    ensures result == ExpectedResult(n, t)
// </vc-spec>
// <vc-code>
{
    if n == 1 {
        if t == "0" {
            result := 10000000000;
        } else {
            result := 20000000000;
        }
    } else if n == 2 {
        if t == "00" {
            result := 0;
        } else if t == "01" {
            result := 9999999999;
        } else if t == "10" {
            result := 10000000000;
        } else {
            result := 10000000000;
        }
    } else {
        var repeat_num := (n + 6) / 3;
        assert repeat_num <= (200000 + 6) / 3 < 100000;
        
        var ref := "";
        var i := 0;
        while i < repeat_num
            invariant 0 <= i <= repeat_num
            invariant |ref| == i * 3
            invariant forall k :: 0 <= k < i ==> k * 3 + 2 < |ref| && ref[k*3] == '1' && ref[k*3+1] == '1' && ref[k*3+2] == '0'
        {
            ref := ref + "110";
            i := i + 1;
        }

        RefEquivalence(repeat_num, ref);
        var expectedRef := seq(repeat_num * 3, i => if i % 3 == 0 then '1' else if i % 3 == 1 then '1' else '0');
        assert ref == expectedRef;

        var base_count := 10000000000 - repeat_num + 2;
        assert base_count > 0;

        if |ref| >= n && ref[0..n] == t {
            var flag_over := if n % 3 == 0 then 1 else 0;
            result := base_count + flag_over;
        } else if |ref| >= n + 1 && ref[1..n+1] == t {
            result := base_count;
        } else if |ref| >= n + 2 && ref[2..n+2] == t {
            var flag_over := if n % 3 == 2 then -1 else 0;
            var temp_result := base_count + flag_over;
            result := if temp_result < 0 then 0 else temp_result;
        } else {
            result := 0;
        }
    }
}
// </vc-code>
