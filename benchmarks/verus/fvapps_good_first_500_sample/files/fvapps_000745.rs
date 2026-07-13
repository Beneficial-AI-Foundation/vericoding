// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_common_ingredients(dish1: Seq<String>, dish2: Seq<String>) -> nat
    decreases dish1.len()
{
    if dish1.len() == 0 {
        0
    } else {
        let count_rest = count_common_ingredients(dish1.skip(1), dish2);
        if dish2.contains(dish1[0]) {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

fn check_similar_dishes(dish1: Vec<String>, dish2: Vec<String>) -> (result: String)
    requires 
        dish1.len() >= 4,
        dish2.len() >= 4,
    ensures 
        ({
            let common_count = count_common_ingredients(dish1@, dish2@);
            if common_count >= 2 { 
                result@ == "similar"@
            } else { 
                result@ == "dissimilar"@
            }
        })
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    /* Test cases would go here:
    let test1_dish1 = vec!["eggs".to_string(), "sugar".to_string(), "flour".to_string(), "salt".to_string()];
    let test1_dish2 = vec!["sugar".to_string(), "eggs".to_string(), "milk".to_string(), "flour".to_string()];
    let result1 = check_similar_dishes(test1_dish1, test1_dish2);
    assert_eq!(result1, "similar");

    let test2_dish1 = vec!["aa".to_string(), "ab".to_string(), "ac".to_string(), "ad".to_string()];
    let test2_dish2 = vec!["ac".to_string(), "ad".to_string(), "ae".to_string(), "af".to_string()];
    let result2 = check_similar_dishes(test2_dish1, test2_dish2);
    assert_eq!(result2, "similar");

    let test3_dish1 = vec!["cookies".to_string(), "sugar".to_string(), "grass".to_string(), "lemon".to_string()];
    let test3_dish2 = vec!["lemon".to_string(), "meat".to_string(), "chili".to_string(), "wood".to_string()];
    let result3 = check_similar_dishes(test3_dish1, test3_dish2);
    assert_eq!(result3, "dissimilar");
    */
}