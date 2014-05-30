# Symbols, Terms, and Alphabets #

A *symbol* is an object which keeps a consistent identity, allowing for comparison with
$=$ and $\neq$. In this text, symbols will be represented with unitalicized, capitalized
strings. For example, $\mathrm{A}$, $\mathrm{Add}$ and $\mathrm{Zero}$ are all symbols.
A *term* is a recursive structure that is constructed by applying a symbol to a list of
term arguments, as if it were a function. The argument list may be omitted if there are 
no arguments. Thus, a lone symbol may be interpreted as a term. For example, using the
set of symbols above, $\mathrm{Zero}$ is a term, equivalent to $\mathrm{Zero}()$. $\mathrm{Add}(\mathrm{Zero}, \mathrm{Zero})$ is a more complex term, constructed by
applying the symbol $\mathrm{Add}$ to two instances of the term $\mathrm{Zero}$.

**Definition 1.** $Alphabet$ is the set of all alphabets.

1. $Alphabet = \mathcal P (Symbol \times \mathbb{N})$

**Definition 2.** For $A \in Alphabet, i \in \mathbb{N}$: $Term_i(A)$ is the set of all
terms with symbols in $A$ and a depth of $i$. $Term^-_i(A)$ is the set of all
terms with symbols in $A$ and a depth less than $i$. $Term(A)$ is the set of all
terms with symbols in $A$.

1. $Term_i(A) = \left\{s(a_1, ..., a_n) \mid (s, n) \in A \wedge a_1, ..., a_n \in 
	Term^-_i(A) \right\}$
2. $Term^-_i(A) = \bigcup^{i - 1}_{j = 0} Term_j(A)$
3. $Term(A) = \bigcup_{j \in \mathbb{N}} Term_j(A)$

**Definition 3.** For $A \in Alphabet$: $System(A)$ is the set of all systems with symbols
in $A$.

1. $System(A) = \left\{R | R \in \mathcal P (Term(A)^2) \wedge extensible(A, R) \right\}$
2. $extensible(A, R) \iff \forall (s, n) \in A. \, 
	\forall (a_1, ..., a_n), (b_1, ... b_n) \in Term(A)^n.$  
	$(a_1, b_1), ..., (a_n, b_n) \in R \implies
	(s (a_1, ..., a_n), s (b_1, ..., b_n)) \in R$