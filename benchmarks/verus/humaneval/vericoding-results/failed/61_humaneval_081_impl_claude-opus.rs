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
/* helper modified by LLM (iteration 5): Add helper to convert grade spec to String */
fn grade_to_string(gpa: i8) -> (result: String)
    ensures result@ == get_letter_grade(gpa as int)
{
    if gpa == 40 {
        "A+".to_string()
    } else if gpa > 37 {
        "A".to_string()
    } else if gpa > 33 {
        "A-".to_string()
    } else if gpa > 30 {
        "B+".to_string()
    } else if gpa > 27 {
        "B".to_string()
    } else if gpa > 23 {
        "B-".to_string()
    } else if gpa > 20 {
        "C+".to_string()
    } else if gpa > 17 {
        "C".to_string()
    } else if gpa > 13 {
        "C-".to_string()
    } else if gpa > 10 {
        "D+".to_string()
    } else if gpa > 7 {
        "D".to_string()
    } else if gpa > 0 {
        "D-".to_string()
    } else {
        "E".to_string()
    }
}
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
    /* code modified by LLM (iteration 5): Use string literals instead of String::new() */
    let mut letter_grades: Vec<String> = Vec::new();
    let mut i = 0;
    
    while i < grades.len()
        invariant
            0 <= i <= grades.len(),
            letter_grades.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] letter_grades[j]@ == get_letter_grade(grades[j] as int),
            valid_letter_grades(letter_grades@),
    {
        let gpa = grades[i];
        let letter_grade = grade_to_string(gpa);
        letter_grades.push(letter_grade);
        i = i + 1;
    }
    
    letter_grades
}
// </vc-code>


}

fn main() {}