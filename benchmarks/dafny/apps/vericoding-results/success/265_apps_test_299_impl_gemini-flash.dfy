// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed duplicate helper definitions and fixed compilation errors. The `sum` function is now correctly defined to calculate the sum of a sequence of integers. The `ChestTotal`, `BicepsTotal`, `BackTotal`, `ValidInput` and `IsWinner` functions/predicates were already defined in the preamble and moved to `vc-helpers` in previous iterations, but were duplicated; they have been removed to resolve compilation errors. The `GetMaximizedMuscleGroup` helper is retained and its logic is slightly refined to exactly match the `IsWinner` conditions.*/
function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

function GetMaximizedMuscleGroup(chestTotal: int, bicepsTotal: int, backTotal: int): string
{
    if chestTotal >= bicepsTotal && chestTotal >= backTotal then "chest"
    else if bicepsTotal > chestTotal && bicepsTotal >= backTotal then "biceps"
    else if backTotal > chestTotal && backTotal > bicepsTotal then "back"
    else "chest" // Default to chest if none of the above (shouldn't happen given IsWinner postcondition)
}
// </vc-helpers>

// <vc-spec>
method FindStrongestMuscleGroup(reps: seq<int>) returns (result: string)
    requires ValidInput(reps)
    ensures result == "chest" || result == "biceps" || result == "back"
    ensures IsWinner(result, reps)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): No changes were made to the method body in this iteration, as helper function duplicates were removed to address compilation errors. The logic for determining the strongest muscle group is already correctly implemented and leverages the `GetMaximizedMuscleGroup` helper function to satisfy the postconditions. */
{
    var chestTotal := ChestTotal(reps);
    var bicepsTotal := BicepsTotal(reps);
    var backTotal := BackTotal(reps);

    result := GetMaximizedMuscleGroup(chestTotal, bicepsTotal, backTotal);

    // The following `if` statements are used to prove the `IsWinner` postcondition.
    // Dafny sometimes needs explicit checks to connect the helper function logic
    // with the postcondition predicate's definition.
    if result == "chest" {
        assert chestTotal >= bicepsTotal && chestTotal >= backTotal;
    } else if result == "biceps" {
        assert bicepsTotal > chestTotal && bicepsTotal >= backTotal;
    } else if result == "back" {
        assert backTotal > chestTotal && backTotal > bicepsTotal;
    }
}
// </vc-code>
