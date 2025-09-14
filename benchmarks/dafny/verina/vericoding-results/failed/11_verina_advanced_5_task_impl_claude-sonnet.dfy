// <vc-preamble>
function ListToNat(l: seq<nat>): nat
    decreases |l|
{
    if |l| == 0 then
        0
    else
        l[0] + 10 * ListToNat(l[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed calculation steps and proof chains for all verification errors */
function pow10(n: nat): nat
{
    if n == 0 then 1 else 10 * pow10(n - 1)
}

lemma SeqAssociativity<T>(a: seq<T>, b: seq<T>, c: seq<T>)
    ensures (a + b) + c == a + (b + c)
{
}

lemma ListToNatAppend(a: seq<nat>, b: seq<nat>)
    requires |a| > 0
    ensures ListToNat(a + b) == ListToNat(a) + ListToNat(b) * pow10(|a|)
{
    if |a| == 1 {
        calc {
            ListToNat(a + b);
            == a[0] + 10 * ListToNat((a + b)[1..]);
            == a[0] + 10 * ListToNat(b);
            == ListToNat(a) + ListToNat(b) * pow10(|a|);
        }
    } else {
        ListToNatAppend(a[1..], b);
        calc {
            ListToNat(a + b);
            == a[0] + 10 * ListToNat((a + b)[1..]);
            == { assert (a + b)[1..] == a[1..] + b; }
            a[0] + 10 * ListToNat(a[1..] + b);
            == { ListToNatAppend(a[1..], b); }
            a[0] + 10 * (ListToNat(a[1..]) + ListToNat(b) * pow10(|a[1..]|));
            == a[0] + 10 * ListToNat(a[1..]) + 10 * ListToNat(b) * pow10(|a| - 1);
            == ListToNat(a) + ListToNat(b) * pow10(|a|);
        }
    }
}

lemma ListToNatBounds(l: seq<nat>)
    requires |l| > 0
    requires forall i :: 0 <= i < |l| ==> l[i] < 10
    ensures ListToNat(l) < pow10(|l|)
{
    if |l| == 1 {
        calc {
            ListToNat(l);
            == l[0];
            < 10;
            == { assert pow10(1) == 10; }
            pow10(|l|);
        }
    } else {
        ListToNatBounds(l[1..]);
        calc {
            ListToNat(l);
            == l[0] + 10 * ListToNat(l[1..]);
            < { assert l[0] < 10; ListToNatBounds(l[1..]); }
            10 + 10 * pow10(|l| - 1);
            == { assert pow10(|l|) == 10 * pow10(|l| - 1); }
            pow10(|l|);
        }
    }
}

lemma ListToNatExtensionZero(l: seq<nat>, n: nat)
    ensures ListToNat(l + seq(n, _ => 0)) == ListToNat(l)
{
    if n == 0 {
        assert l + seq(0, _ => 0) == l;
    } else {
        ListToNatExtensionZero(l, n - 1);
        SeqAssociativity(l, seq(n - 1, _ => 0), [0]);
        assert l + seq(n, _ => 0) == (l + seq(n - 1, _ => 0)) + [0];
        var temp := l + seq(n - 1, _ => 0);
        if |temp| > 0 {
            ListToNatAppend(temp, [0]);
            assert ListToNat(temp + [0]) == ListToNat(temp) + ListToNat([0]) * pow10(|temp|);
            assert ListToNat([0]) == 0;
        }
        assert ListToNat(l + seq(n, _ => 0)) == ListToNat(l);
    }
}

predicate DigitSum(a: seq<nat>, b: seq<nat>, result: seq<nat>, carry: nat)
    requires |a| == |b| == |result|
    requires carry <= 1
{
    if |a| == 0 then carry == 0
    else
        var sum := a[0] + b[0] + carry;
        result[0] == sum % 10 &&
        sum / 10 <= 1 &&
        DigitSum(a[1..], b[1..], result[1..], sum / 10)
}

function FinalCarry(a: seq<nat>, b: seq<nat>, carry: nat): nat
    requires |a| == |b|
    requires carry <= 1
    requires forall i :: 0 <= i < |a| ==> a[i] < 10 && b[i] < 10
{
    if |a| == 0 then carry
    else
        var sum := a[0] + b[0] + carry;
        FinalCarry(a[1..], b[1..], sum / 10)
}

lemma FinalCarryZero(a: seq<nat>, b: seq<nat>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> a[i] < 10 && b[i] < 10
    ensures FinalCarry(a, b, 0) == 0
{
    if |a| == 0 {
        assert FinalCarry(a, b, 0) == 0;
    } else {
        var sum := a[0] + b[0];
        assert sum < 20;
        assert sum / 10 <= 1;
        FinalCarryZero(a[1..], b[1..]);
    }
}

lemma DigitSumCorrect(a: seq<nat>, b: seq<nat>, result: seq<nat>, carry: nat, finalCarry: nat)
    requires |a| == |b| == |result|
    requires carry <= 1
    requires forall i :: 0 <= i < |a| ==> a[i] < 10 && b[i] < 10
    requires DigitSum(a, b, result, carry)
    requires finalCarry == FinalCarry(a, b, carry)
    ensures ListToNat(result) + finalCarry * pow10(|result|) == ListToNat(a) + ListToNat(b) + carry
{
    if |a| == 0 {
        assert carry == 0;
        assert finalCarry == 0;
        assert ListToNat(result) == 0;
        assert ListToNat(a) + ListToNat(b) == 0;
    } else {
        var sum := a[0] + b[0] + carry;
        var newCarry := sum / 10;
        DigitSumCorrect(a[1..], b[1..], result[1..], newCarry, FinalCarry(a[1..], b[1..], newCarry));
        calc {
            ListToNat(result) + finalCarry * pow10(|result|);
            == result[0] + 10 * ListToNat(result[1..]) + finalCarry * pow10(|result|);
            == sum % 10 + 10 * ListToNat(result[1..]) + finalCarry * pow10(|result|);
            == sum % 10 + 10 * (ListToNat(a[1..]) + ListToNat(b[1..]) + newCarry - FinalCarry(a[1..], b[1..], newCarry) * pow10(|a| - 1)) + finalCarry * pow10(|result|);
            == ListToNat(a) + ListToNat(b) + carry;
        }
    }
}

lemma DigitAdditionCorrectness(a: seq<nat>, b: seq<nat>, result: seq<nat>)
    requires |a| == |b| == |result|
    requires forall i :: 0 <= i < |a| ==> a[i] < 10 && b[i] < 10
    requires forall i :: 0 <= i < |result| ==> result[i] < 10
    requires DigitSum(a, b, result, 0)
    ensures ListToNat(result) == ListToNat(a) + ListToNat(b)
{
    FinalCarryZero(a, b);
    DigitSumCorrect(a, b, result, 0, FinalCarry(a, b, 0));
    assert ListToNat(result) + FinalCarry(a, b, 0) * pow10(|result|) == ListToNat(a) + ListToNat(b);
    assert FinalCarry(a, b, 0) == 0;
}
// </vc-helpers>

// <vc-spec>
method AddTwoNumbers(l1: array<nat>, l2: array<nat>) returns (result: array<nat>)
    requires 
        l1.Length > 0 &&
        l2.Length > 0 &&
        (forall i :: 0 <= i < l1.Length ==> l1[i] < 10) &&
        (forall i :: 0 <= i < l2.Length ==> l2[i] < 10) &&
        (l1[l1.Length - 1] != 0 || (l1.Length == 1 && l1[0] == 0)) &&
        (l2[l2.Length - 1] != 0 || (l2.Length == 1 && l2[0] == 0))
    ensures
        result.Length > 0 &&
        ListToNat(result[..]) == ListToNat(l1[..]) + ListToNat(l2[..]) &&
        (forall i :: 0 <= i < result.Length ==> result[i] < 10) &&
        (result[result.Length - 1] != 0 || (l1.Length == 1 && l1[0] == 0 && l2.Length == 1 && l2[0] == 0 && result.Length == 1 && result[0] == 0))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed digit sum predicate satisfaction and carry computation */
{
    var maxLen := if l1.Length > l2.Length then l1.Length else l2.Length;
    var tempResult := new nat[maxLen + 1];
    var carry: nat := 0;
    var i := 0;
    
    while i < maxLen
        invariant 0 <= i <= maxLen
        invariant carry <= 1
        invariant forall j :: 0 <= j < i ==> tempResult[j] < 10
        invariant forall j :: 0 <= j < i ==> 
            var digit1 := if j < l1.Length then l1[j] else 0;
            var digit2 := if j < l2.Length then l2[j] else 0;
            digit1 < 10 && digit2 < 10
    {
        var digit1 := if i < l1.Length then l1[i] else 0;
        var digit2 := if i < l2.Length then l2[i] else 0;
        var sum := digit1 + digit2 + carry;
        tempResult[i] := sum % 10;
        carry := sum / 10;
        assert sum < 30;
        assert carry <= 2;
        if digit1 < 10 && digit2 < 10 && carry <= 1 {
            assert sum < 21;
            assert carry <= 1;
        }
        i := i + 1;
    }
    
    tempResult[maxLen] := carry;
    
    var actualLen := if carry == 0 then maxLen else maxLen + 1;
    if actualLen == 0 {
        actualLen := 1;
    }
    
    result := new nat[actualLen];
    i := 0;
    while i < actualLen
        invariant 0 <= i <= actualLen
        invariant forall j :: 0 <= j < i ==> result[j] == tempResult[j]
        invariant forall j :: 0 <= j < i ==> result[j] < 10
    {
        result[i] := tempResult[i];
        i := i + 1;
    }
    
    var l1_extended := l1[..] + seq(maxLen - l1.Length, _ => 0);
    var l2_extended := l2[..] + seq(maxLen - l2.Length, _ => 0);
    
    ListToNatExtensionZero(l1[..], maxLen - l1.Length);
    ListToNatExtensionZero(l2[..], maxLen - l2.Length);
    
    var tempSeq := tempResult[..maxLen];
    
    assert forall j :: 0 <= j < maxLen ==> 
        var digit1 := if j < l1.Length then l1[j] else 0;
        var digit2 := if j < l2.Length then l2[j] else 0;
        l1_extended[j] == digit1 && l2_extended[j] == digit2;
    
    assert forall j :: 0 <= j < maxLen ==> l1_extended[j] < 10 && l2_extended[j] < 10;
    assert forall j :: 0 <= j < maxLen ==> tempSeq[j] < 10;
    
    ghost var digitSumHolds := forall pos :: 0 <= pos < maxLen ==>
        var digit1 := l1_extended[pos];
        var digit2 := l2_extended[pos];
        var localCarry := if pos == 0 then 0 else 
            (if pos - 1 < l1.Length then l1[pos - 1] else 0) +
            (if pos - 1 < l2.Length then l2[pos - 1] else 0);
        tempSeq[pos] == (digit1 + digit2) % 10;
    
    FinalCarryZero(l1_extended, l2_extended);
    
    if carry == 0 {
        assert actualLen == maxLen;
        assert result[..] == tempSeq;
        assert ListToNat(l1_extended) == ListToNat(l1[..]);
        assert ListToNat(l2_extended) == ListToNat(l2[..]);
        assert ListToNat(result[..]) == ListToNat(l1[..]) + ListToNat(l2[..]);
    } else {
        assert actualLen == maxLen + 1;
        assert result[..] == tempResult[..];
        if |tempSeq| > 0 {
            ListToNatAppend(tempSeq, [carry]);
            assert ListToNat(result[..]) == ListToNat(tempSeq) + carry * pow10(maxLen);
        }
        assert ListToNat(result[..]) == ListToNat(l1[..]) + ListToNat(l2[..]);
    }
}
// </vc-code>
