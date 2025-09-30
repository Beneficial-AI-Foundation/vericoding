function ChestTotal(reps: seq<int>): int
{
    sum(seq(|reps|, i requires 0 <= i < |reps| => if i % 3 == 0 then reps[i] else 0))
}

function BicepsTotal(reps: seq<int>): int
{
    sum(seq(|reps|, i requires 0 <= i < |reps| => if i % 3 == 1 then reps[i] else 0))
}

function BackTotal(reps: seq<int>): int
{
    sum(seq(|reps|, i requires 0 <= i < |reps| => if i % 3 == 2 then reps[i] else 0))
}

predicate ValidInput(reps: seq<int>)
{
    |reps| > 0 && forall i | 0 <= i < |reps| :: reps[i] > 0
}

predicate IsWinner(muscle: string, reps: seq<int>)
    requires ValidInput(reps)
{
    var chestTotal := ChestTotal(reps);
    var bicepsTotal := BicepsTotal(reps);
    var backTotal := BackTotal(reps);

    match muscle
        case "chest" => chestTotal >= bicepsTotal && chestTotal >= backTotal
        case "biceps" => bicepsTotal > chestTotal && bicepsTotal >= backTotal
        case "back" => backTotal > chestTotal && backTotal > bicepsTotal
        case _ => false
}

// <vc-helpers>
function sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum(s[1..])
}
// </vc-helpers>

// <vc-spec>
method FindStrongestMuscleGroup(reps: seq<int>) returns (result: string)
    requires ValidInput(reps)
    ensures result == "chest" || result == "biceps" || result == "back"
    ensures IsWinner(result, reps)
// </vc-spec>
// <vc-code>
{
    var chestTotal := ChestTotal(reps);
    var bicepsTotal := BicepsTotal(reps);
    var backTotal := BackTotal(reps);
    
    if chestTotal >= bicepsTotal && chestTotal >= backTotal {
        result := "chest";
    } else if bicepsTotal >= backTotal {
        result := "biceps";
    } else {
        result := "back";
    }
}
// </vc-code>

