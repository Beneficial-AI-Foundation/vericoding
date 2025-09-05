# Your Task
You have a Petri dish with bacteria, and you are preparing to dive into the harsh micro-world. But, unfortunately, you don't have any microscope nearby, so you can't watch them.

You know that you have `n` bacteria in the Petri dish and size of the i-th bacteria is bacteriai. Also you know intergalactic positive integer constant `K`.

The i-th bacteria can swallow the j-th bacteria if and only if bacteriai > bacteriaj and bacteriai ≤ bacteriaj + K. The j-th bacteria disappear, but the i-th bacteria doesn't change its size.

Since you don't have a microscope, you can only guess the minimal possible number of bacteria that will remain in your Petri dish when you finally find a microscope.

```python
micro_world([101, 53, 42, 102, 101, 55, 54], 1) == 3
micro_world([20, 15, 10, 15, 20, 25], 5) == 1
```

___

# Explanation
```python
bacteria = [101, 53, 42, 102, 101, 55, 54]
K = 1
```

```if:cpp
The one of possible sequences of swallows is: {101,53,42,102,101,55,54} → {101,53,42,102,55,54} → {101,42,102,55,54} → {42,102,55,54} → {42,102,55}. In total there are 3 bacteria remaining.
```
```if:python,ruby,javascript
The one of possible sequences of swallows is: [101,53,42,102,101,55,54] → [101,53,42,102,55,54] → [101,42,102,55,54] → [42,102,55,54] → [42,102,55]. In total there are 3 bacteria remaining.
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
