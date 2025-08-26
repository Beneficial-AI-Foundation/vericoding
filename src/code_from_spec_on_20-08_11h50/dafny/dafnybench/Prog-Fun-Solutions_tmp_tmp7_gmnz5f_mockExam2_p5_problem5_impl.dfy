ghost function f(n: int): int {
  if n < 0 then 0 else 3*f(n-5) + n
}