Inductive ℕ :=
	| ζ : ℕ
	| σ : ℕ -> ℕ.

Fixpoint addition (a b : ℕ) : ℕ :=
	match b with
	| ζ   => a                (* Base *)
	| σ β => σ (addition a β) (* Recursion *)
	end.

Infix "﬩" := addition (at level 50, left associativity).

Fixpoint multiplication (a b : ℕ) : ℕ :=
	match b with
	| ζ   => ζ                        (* Base *)
	| σ β => (multiplication a β) ﬩ a (* Recursion *)
	end.

Infix "×" := multiplication (at level 51, left associativity).

Fixpoint exponenciation (a b : ℕ) : ℕ :=
	match b with
	| ζ   => σ ζ                      (* Base *)
	| σ β => (exponenciation a β) × a (* Recursion *)
	end.

Infix "↑" := exponenciation (at level 52, left associativity).