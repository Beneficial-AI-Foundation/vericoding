function possible(n: int, foodTypes: seq<int>, days: int): bool
    requires n >= 0
    requires days >= 0
    requires forall i :: 0 <= i < |foodTypes| ==> foodTypes[i] >= 1
{
    if days == 0 then true
    else
        var totalParticipants := countTotalParticipants(foodTypes, days, 1);
        totalParticipants >= n
}

function countTotalParticipants(foodTypes: seq<int>, days: int, currentType: int): int
    requires days >= 0
    requires currentType >= 1
    decreases 101 - currentType
    ensures countTotalParticipants(foodTypes, days, currentType) >= 0
    ensures days > 0 ==> countTotalParticipants(foodTypes, days + 1, currentType) <= countTotalParticipants(foodTypes, days, currentType)
{
    if currentType > 100 then 0
    else
        var packagesOfThisType := countPackages(foodTypes, currentType);
        var participantsForThisType := if days > 0 then packagesOfThisType / days else 0;
        participantsForThisType + countTotalParticipants(foodTypes, days, currentType + 1)
}

function countPackages(foodTypes: seq<int>, targetType: int): int
    requires targetType >= 1
    ensures countPackages(foodTypes, targetType) >= 0
    ensures countPackages(foodTypes, targetType) <= |foodTypes|
{
    if |foodTypes| == 0 then 0
    else if foodTypes[0] == targetType then 1 + countPackages(foodTypes[1..], targetType)
    else countPackages(foodTypes[1..], targetType)
}

// <vc-helpers>
predicate isPossible(n: int, foodTypes: seq<int>, days: int) {
    if days == 0 then true
    else
        var totalParticipants := countTotalParticipants(foodTypes, days, 1);
        totalParticipants >= n
}

lemma {:opaque} isPossible_impossible_lemma(n: int, foodTypes: seq<int>, days: int)
    requires isPossible(n, foodTypes, days) == true
    ensures isPossible(n, foodTypes, days + 1) == false
{
    calc {
        isPossible(n, foodTypes, days);
        true;
        == { reveal isPossible; }
        (if days == 0 then true else
            var totalParticipants := countTotalParticipants(foodTypes, days, 1);
            totalParticipants >= n
        );
        { 
            if days != 0 {
                assert countTotalParticipants(foodTypes, days + 1, 1) <= countTotalParticipants(foodTypes, days, 1);
            }
        }
        (if days == 0 then true else
            countTotalParticipants(foodTypes, days + 1, 1) >= n
        );
        == { reveal isPossible; }
        isPossible(n, foodTypes, days + 1);
    }
    assert false;
}

lemma {:opaque} possible_monotonicity(n: int, foodTypes: seq<int>, d1: int, d2: int)
    requires d1 >= d2
    requires isPossible(n, foodTypes, d2) == true
    ensures isPossible(n, foodTypes, d1) == true
{
    if d1 == d2 {
    } else if d2 == 0 {
        assert isPossible(n, foodTypes, d1) == true;
    } else {
        calc {
            countTotalParticipants(foodTypes, d1, 1);
            <= countTotalParticipants(foodTypes, d2, 1);
            { reveal isPossible; }
            n;
        }
        reveal isPossible;
        assert countTotalParticipants(foodTypes, d1, 1) >= n;
    }
}

lemma possible_implies_possible_for_less(n: int, foodTypes: seq<int>, d: int)
    requires d > 0
    requires isPossible(n, foodTypes, d) == true
    ensures isPossible(n, foodTypes, d - 1) == true
{
    possible_monotonicity(n, foodTypes, d - 1, d);
}

ghost method findMinDays(n: int, foodTypes: seq<int>) returns (minDays: int)
    requires 1 <= n <= 100
    requires forall i :: 0 <= i < |foodTypes| ==> 1 <= foodTypes[i] <= 100
    ensures 0 <= minDays <= |foodTypes|
    ensures minDays > 0 ==> isPossible(n, foodTypes, minDays) == true
    ensures minDays == 0 ==> isPossible(n, foodTypes, 1) == false
    ensures forall d :: d > minDays ==> isPossible(n, foodTypes, d) == true
    ensures forall d :: 0 < d < minDays ==> isPossible(n, foodTypes, d) == false
{
    minDays := 0;
    if isPossible(n, foodTypes, 1) {
        minDays := |foodTypes|;
        while minDays > 0
            invariant 0 <= minDays <= |foodTypes|
            invariant isPossible(n, foodTypes, minDays) == true
            invariant forall d :: minDays < d <= |foodTypes| ==> isPossible(n, foodTypes, d) == true
        {
            if isPossible(n, foodTypes, minDays - 1) {
                minDays := minDays - 1;
            } else {
                break;
            }
        }
        assert minDays == 0 || isPossible(n, foodTypes, minDays) == true;
        assert forall d :: d > minDays ==> isPossible(n, foodTypes, d) == true;
        assert forall d :: 0 < d < minDays ==> isPossible(n, foodTypes, d) == false;
    } else {
        assert minDays == 0;
        assert isPossible(n, foodTypes, 1) == false;
    }
}

lemma possible_equivalence_lemma(n: int, foodTypes: seq<int>, days: int)
    ensures possible(n, foodTypes, days) == isPossible(n, foodTypes, days)
{
    reveal isPossible();
    calc {
        possible(n, foodTypes, days);
        (if days == 0 then true else
            var totalParticipants := countTotalParticipants(foodTypes, days, 1);
            totalParticipants >= n
        );
        isPossible(n, foodTypes, days);
    }
}

method findMinDays_nonGhost(n: int, foodTypes: seq<int>) returns (minDays: int)
    requires 1 <= n <= 100
    requires forall i :: 0 <= i < |foodTypes| ==> 1 <= foodTypes[i] <= 100
    ensures 0 <= minDays <= |foodTypes|
    ensures minDays > 0 ==> possible(n, foodTypes, minDays)
    ensures minDays == 0 ==> !possible(n, foodTypes, 1)
    ensures forall d :: d > minDays ==> possible(n, foodTypes, d)
    ensures forall d :: 0 < d < minDays ==> !possible(n, foodTypes, d)
{
    var g_minDays := findMinDays(n, foodTypes);
    minDays := g_minDays;
    possible_equivalence_lemma(n, foodTypes, minDays);
    if minDays > 0 {
        possible_equivalence_lemma(n, foodTypes, 1);
    }
    if minDays > 0 {
        forall d | d > minDays ensures possible(n, foodTypes, d) {
            possible_equivalence_lemma(n, foodTypes, d);
            assert isPossible(n, foodTypes, d) == true;
        }
        forall d | 0 < d < minDays ensures !possible(n, foodTypes, d) {
            possible_equivalence_lemma(n, foodTypes, d);
            assert isPossible(n, foodTypes, d) == false;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, foodTypes: seq<int>) returns (result: int)
    requires 1 <= n <= 100
    requires 1 <= m <= 100
    requires |foodTypes| == m
    requires forall i :: 0 <= i < |foodTypes| ==> 1 <= foodTypes[i] <= 100
    ensures result >= 0
    ensures result <= m
    ensures result > 0 ==> possible(n, foodTypes, result)
    ensures !possible(n, foodTypes, result + 1)
    ensures forall d :: d > result ==> !possible(n, foodTypes, d)
// </vc-spec>
// <vc-code>
{
    var min_p := findMinDays_nonGhost(n, foodTypes);
    result := min_p;
}
// </vc-code>

