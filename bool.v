Inductive 𝔹 :=
	| t
	| f.

Notation "⊤" := t.
Notation "⊥" := f.

Definition not (b : 𝔹) : 𝔹 := 
	match b with
	| ⊤ => ⊥
	| ⊥ => ⊥
	end.

Definition conjunction (b₁ b₂ : 𝔹) : 𝔹 :=
	match b₁ with
	| ⊤ => b₂
	| ⊥ => ⊥
	end.

Definition disjunction (b₁ b₂ : 𝔹) : 𝔹 :=
	match b₁ with
	| ⊤ => ⊤
	| ⊥ => b₂
	end.

Definition implication (b₁ b₂ : 𝔹) : 𝔹 :=
	match b₁ with
	| ⊤ => b₂
	| ⊥ => ⊤
	end.

Notation "¬" := not.
Infix "∧" := conjunction (at level 80, right associativity).
Infix "∨" := disjunction (at level 85, right associativity).
Infix "→" := implication (at level 99, right associativity).

Lemma demorgan₁ : forall p q : 𝔹, ¬(p ∨ q) = (¬p ∧ ¬q).
Proof.
	intros [][].
		- simpl. reflexivity.
		- simpl. reflexivity. 
		- simpl. reflexivity.
		- simpl. reflexivity.
Qed.

Lemma demorgan₂ : forall p q : 𝔹, ¬(p ∧ q) = (¬p ∨ ¬q).
Proof.
	intros [][].
		- simpl. reflexivity.
		- simpl. reflexivity. 
		- simpl. reflexivity.
		- simpl. reflexivity.
Qed.
