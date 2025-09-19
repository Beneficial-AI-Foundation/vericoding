-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sayHello (name : String) : String := sorry

theorem say_hello_returns_string {name : String} (h : name.length > 0) :
  let greeting := sayHello name
  String.length greeting > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem say_hello_starts_with_hello {name : String} (h : name.length > 0) :
  let greeting := sayHello name
  String.startsWith greeting "Hello, " = true := sorry

theorem say_hello_ends_with_name {name : String} (h : name.length > 0) :
  let greeting := sayHello name
  String.endsWith greeting name = true := sorry

theorem say_hello_length {name : String} (h : name.length > 0) :
  let greeting := sayHello name
  String.length greeting = String.length "Hello, " + String.length name := sorry
-- </vc-theorems>