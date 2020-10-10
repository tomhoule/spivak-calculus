import data.real.basic

variables { x x₀ y y₀ ε : ℝ }

example :
abs (x - x₀) < ε / 2 ∧ abs (y - y₀) < ε / 2 →
abs ((x+y) - (x₀+y₀)) < ε :=
begin
intro h,
have absSum : abs ((x - x₀) + (y - y₀)) ≤ abs (x - x₀) + abs (y - y₀), from abs_add (x - x₀) (y - y₀),
have : (x - x₀) + (y - y₀) = (x+y) - (x₀+y₀), by linarith only [],
have left : abs ((x+y) - (x₀+y₀)) ≤ abs (x - x₀) + abs (y - y₀), by rwa [this] at absSum,
have : abs (x - x₀) + abs (y - y₀) <  ε / 2 + ε / 2, from add_lt_add h.left h.right,
have right : abs (x - x₀) + abs (y - y₀) <  ε, by linarith only [this],
exact lt_of_le_of_lt left right
end

example :
abs (x - x₀) < ε / 2 ∧ abs (y - y₀) < ε / 2 →
abs ((x - y) - (x₀ - y₀)) < ε :=
begin
intro h,
sorry
end
