// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn get_letter_grade(gpa: int) -> Seq<char> {
    if gpa == 40 { seq!['A', '+'] }
    else if gpa > 37 { seq!['A'] }
    else if gpa > 33 { seq!['A', '-'] }
    else if gpa > 30 { seq!['B', '+'] }
    else if gpa > 27 { seq!['B'] }
    else if gpa > 23 { seq!['B', '-'] }
    else if gpa > 20 { seq!['C', '+'] }
    else if gpa > 17 { seq!['C'] }
    else if gpa > 13 { seq!['C', '-'] }
    else if gpa > 10 { seq!['D', '+'] }
    else if gpa > 7 { seq!['D'] }
    else if gpa > 0 { seq!['D', '-'] }
    else { seq!['E'] }
}

spec fn valid_letter_grades(grades: Seq<String>) -> bool {
    forall|i: int| 0 <= i < grades.len() ==> {
        let grade = #[trigger] grades[i]@;
        grade == seq!['A', '+'] || grade == seq!['A'] || grade == seq!['A', '-'] ||
        grade == seq!['B', '+'] || grade == seq!['B'] || grade == seq!['B', '-'] ||
        grade == seq!['C', '+'] || grade == seq!['C'] || grade == seq!['C', '-'] ||
        grade == seq!['D', '+'] || grade == seq!['D'] || grade == seq!['D', '-'] ||
        grade == seq!['E']
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numerical_letter_grade(grades: Vec<i8>) -> (letter_grades: Vec<String>)
    ensures 
        letter_grades.len() == grades.len() &&
        (forall|i: int| 0 <= i < grades.len() ==> 
            #[trigger] letter_grades[i]@ == get_letter_grade(grades[i] as int)) &&
        valid_letter_grades(letter_grades@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix indexing in exec code using grades[i], and build Strings directly by matching score logic without relying on spec Seq */
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < grades.len()
        invariant
            result@.len() == i,
            forall |j: int| 0 <= j < i ==> #[trigger] result@[j]@ == get_letter_grade(grades@[j] as int)
        decreases grades.len() - i
    {
        let score = grades[i];
        let grade_str = if score == 40 {
            "A+".to_string()
        } else if score > 37 {
            "A".to_string()
        } else if score > 33 {
            "A-".to_string()
        } else if score > 30 {
            "B+".to_string()
        } else if score > 27 {
            "B".to_string()
        } else if score > 23 {
            "B-".to_string()
        } else if score > 20 {
            "C+".to_string()
        } else if score > 17 {
            "C".to_string()
        } else if score > 13 {
            "C-".to_string()
        } else if score > 10 {
            "D+".to_string()
        } else if score > 7 {
            "D".to_string()
        } else if score > 0 {
            "D-".to_string()
        } else {
            "E".to_string()
        };
        result.push(grade_str);
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}