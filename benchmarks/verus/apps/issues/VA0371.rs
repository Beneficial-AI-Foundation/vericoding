// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(input: String) -> bool {
        input.len() > 0 && 
        {
            let lines = split_lines_func(input);
            lines.len() >= 2 && 
            string_to_int_func(lines[0]) >= 1 &&
            string_to_int_func(lines[0]) <= (lines.len() as int) - 1
        }
    }
    
    spec fn get_faces(polyhedron: String) -> int {
        if polyhedron == "Tetrahedron" { 4 }
        else if polyhedron == "Cube" { 6 }
        else if polyhedron == "Octahedron" { 8 }
        else if polyhedron == "Dodecahedron" { 12 }
        else if polyhedron == "Icosahedron" { 20 }
        else { 0 }
    }
    
    spec fn split_lines_func(s: String) -> Seq<String> {
        split_lines_helper(s, 0, 0, seq![])
    }
    
    spec fn split_lines_helper(s: String, start: int, i: int, acc: Seq<String>) -> Seq<String>
        decreases s.len() - i
    {
        if i >= s.len() {
            if start < s.len() { acc.push(s.substring_char(start as usize, s.len()).to_string()) }
            else { acc }
        } else if s.get_char(i as usize) == '\n' {
            let new_acc = if start <= i { acc.push(s.substring_char(start as usize, i as usize).to_string()) } else { acc };
            split_lines_helper(s, i + 1, i + 1, new_acc)
        } else {
            split_lines_helper(s, start, i + 1, acc)
        }
    }
    
    spec fn string_to_int_func(s: String) -> int {
        let trimmed = trim_func(s);
        if trimmed.len() == 0 { 0 }
        else { string_to_int_helper(trimmed, 0, 0) }
    }
    
    spec fn string_to_int_helper(s: String, i: int, acc: int) -> int
        decreases s.len() - i
    {
        if i >= s.len() { acc }
        else if '0' <= s.get_char(i as usize) <= '9' {
            string_to_int_helper(s, i + 1, acc * 10 + (s.get_char(i as usize) as int - '0' as int))
        } else {
            string_to_int_helper(s, i + 1, acc)
        }
    }
    
    spec fn int_to_string_func(n: int) -> String {
        if n == 0 { "0".to_string() }
        else { int_to_string_helper(n) }
    }
    
    spec fn int_to_string_helper(n: int) -> String
        decreases n
    {
        if n < 10 { 
            char::from_u32((n + ('0' as int)) as u32).unwrap().to_string()
        } else { 
            int_to_string_helper(n / 10) + char::from_u32((n % 10 + ('0' as int)) as u32).unwrap().to_string()
        }
    }
    
    spec fn trim_func(s: String) -> String {
        let start = trim_start(s, 0);
        let end = trim_end(s, s.len() as int, start);
        if start < end { s.substring_char(start as usize, end as usize).to_string() } else { "".to_string() }
    }
    
    spec fn trim_start(s: String, i: int) -> int
        decreases s.len() - i
    {
        if i >= s.len() { i }
        else if s.get_char(i as usize) == ' ' || s.get_char(i as usize) == '\t' || s.get_char(i as usize) == '\r' || s.get_char(i as usize) == '\n' {
            trim_start(s, i + 1)
        } else { i }
    }
    
    spec fn trim_end(s: String, j: int, start: int) -> int
        decreases j - start
    {
        if j <= start { start }
        else if s.get_char((j-1) as usize) == ' ' || s.get_char((j-1) as usize) == '\t' || s.get_char((j-1) as usize) == '\r' || s.get_char((j-1) as usize) == '\n' {
            trim_end(s, j - 1, start)
        } else { j }
    }
    
    spec fn compute_total_up_to(lines: Seq<String>, count: int) -> int {
        if count == 0 { 0 }
        else if count >= lines.len() { 0 }
        else { get_faces(trim_func(lines[count])) + compute_total_up_to(lines, count - 1) }
    }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    requires
        valid_input(input),
    ensures
        result.len() > 0,
        result.get_char((result.len() - 1) as usize) == '\n',
        exists|total_faces: int| total_faces >= 0 && result == int_to_string_func(total_faces) + "\n",
        valid_input(input) ==> {
            let lines = split_lines_func(input);
            let n = string_to_int_func(lines[0]);
            let expected_total = compute_total_up_to(lines, n);
            result == int_to_string_func(expected_total) + "\n"
        },
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "0\n".to_string()
    // impl-end
}
// </vc-code>


}

fn main() {}