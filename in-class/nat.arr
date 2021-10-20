# data Foo: Foo end


data Nat:
  | O
  | S(n :: Nat)
end

data Zero: end

data One: tt end

data Pair<A, B>: pair(a :: A, b :: B) end

fun nat-plus(n :: Nat, m :: Nat) -> Nat:
  cases (Nat) n:
    | O => m                    # n = O
    | S(x) => S(nat-plus(x, m)) # n = S(x)
  end
end


# nat-plus(O, S(O))

# =>

# cases (Nat) O:
# | O => S(O)
# | S(nn) => S(nat-plus(nn, S(O)))
# end

# =>

# S(O)

# nat-plus(S(O), S(O))

# =>

# cases (Nat) S(O):
# | O => S(O)
# | S(nn) => S(nat-plus(nn, S(O)))
# end

# =>

# S(nat-plus(O, S(O)))

# =>

# S(S(O))


fun pred(n :: Nat) -> Nat:
  cases (Nat) n:
    | O => raise("pred of O")
    | S(nn) => nn
  end
end

#|
   Theorem: ∀ n :: Nat, nat-plus(n, O) = n.
   Proof by induction.

   Base case (n=O).
   nat-plus(O, O) =
   cases (Nat) O:
    | O => O
    | S(nn) => S(nat-plus(nn, O))
    end =
   O

   Inductive case (n = S(nn)).
   IH: nat-plus(nn, O) = nn
   Goal: nat-plus(S(nn), O) = S(nn)
   nat-plus(S(nn), O) =
   cases (Nat) S(nn):
    | O => O
    | S(nn) => S(nat-plus(nn, O))
   end =
   S(nat-plus(nn, O)) =
   S(nn)
|#

fun number-to-nat(n :: Number) -> Nat:
  if n <= 0:
    O
  else:
    S(number-to-nat(n - 1))
  end
end

number-to-nat(5)
