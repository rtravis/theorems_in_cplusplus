/*
 * theorem.cpp
 *
 *  Created on: Dec 22, 2019
 *      Author: Robert Zavalczki
 */
#include "theorem_util.hpp"

#include <cstddef>
#include <functional>
#include <type_traits>
#include <utility>


#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#pragma GCC diagnostic ignored "-Wunused-variable"

/*
 * ## Glossary
 *
 * ###
 * A type is a label associated to a thing.
 *
 * We will use the notation 'x : X' to write that x has the type X (like
 * in set theory, Pascal or ML). For example: x : Int, Int : Set.
 *
 * ###
 * A type constructor can create types from other types or values. E.g.
 * std::vector is not a type, it is a type constructor. Given the
 * 'std::vector' type constructor and another type 'int' we can
 * construct the type std::vector<int>.
 *
 * ###
 * A data constructor creates data values. E.g. in C++ 'true' and
 * 'false' are the data constructors for the type 'bool'.
 * 'std::vector<int>::vector' is a data constructor for the type
 * 'std::vector<int>'.
 *
 * ###
 * We will use the arrow (->) to denote a function (either at type or at
 * value level).
 *
 * Example 1: 'Int -> Int' is a function that takes an 'Int' and returns
 * an 'Int'.
 *
 * Example 2: 'Int -> Int -> Int' is a function that takes an 'Int' and
 * returns another function from 'Int' to 'Int'. This can be viewed also
 * as a function that takes 2 'Int' parameters and returns an 'Int'.
 *
 * Example 3: std::vector : Set -> Set, std::vector is a function that
 * takes a type and returns another type (int -> std::vector<int>).
 *
 * ###
 * A datatype family is a set of related types.
 * E.g. IntArray : size_t -> Set defined as:
 *
 *      template<size_t N> using IntArray = std::array<int, N>;
 *
 * is a family of types indexed by size_t values.
 */

namespace peano {

/*
 * 'Natural' represents a set of data types to model the natural
 * numbers.
 *
 *  Each natural number will be represented by a distinct C++ type that
 *  satisfies the 'Natural' constraint.
 */

// 'Nat' is a helper base class that we use to define the Natural
// constraint.
class Nat;

// We need to be able to constrain template parameters in order to:
//
// 1. restrict ad-hoc polymorphism and try to model parametric
//    polymorphism. Otherwise malicious or ignorant users could
//    specialize our templates in a wrong way.
// 2. to 'typecheck' the types that can be passed to our template
//    classes (type constructors).
//
// To achieve this we use the 'concepts' feature that is available in
// the C++20 language standard.
template<typename N>
concept Natural = std::is_base_of_v<Nat, N> && !std::is_same_v<N, Nat>;

// Nat : Set
class Nat {
	friend struct Zero;
	template<Natural N> friend struct Suc;
	// The constructor is private so that only friends can inherit this
	// class and no 'Nat' values can be constructed directly.
	Nat() = default;
};

// Zero : Natural
// 'Zero' is the first of the two type constructors for the 'Natural'
// types. It defines a concrete type that satisfies the 'Natural'
// constraint. We can create data values of type Zero using the
// Zero::Zero data constructor.
struct Zero : Nat {};

// Suc : Natural -> Natural
// Suc, short for successor, is the second type constructor for the
// 'Natural' types. 'Suc' is a type constructor that takes a 'Natural'
// as parameter.
template<Natural N> struct Suc : Nat {};

// The types in the Natural data type family are singleton types (they
// are like void or nullptr_t). Each of these types can conceptually
// have a single data value.

static void test_naturals() {
	// using BadType1 = Suc<int>; <- error: 'int' is not a 'Natural'
	// using BadType2 = Suc<Nat>; <- error: 'Nat' is not a 'Natural'
	// auto n = Nat(); <- error: Nat::Nat is private
	using One = Suc<Zero>;
	using Two = Suc<One>; // or Suc<Suc<Zero>>
	auto zero = Zero();
	auto one = One();
	auto two = Two();
	// one = two; <- error: no match for 'operator='
	//        (operand types are 'Suc<Zero>' and 'Suc<Suc<Zero> >'
	one = One(); // this assignment is fine
	Nat x = One(); // Bad, but possible. We could have disabled this.
}

// Let's implement addition on the previously defined natural numbers

/*
 * Addition on natural numbers can be defined as a recursive function.
 *
 *    _+_ : Natural -> Natural -> Natural
 *    zero + m = m
 *    suc n + m = suc (n + m)
 */
template<Natural N, Natural M>
struct AddHelper;

// pattern match on: 0 + 'm', the result is 'm'
template<Natural N>
struct AddHelper<Zero, N> {
	using type = N;
};

// pattern match on: suc n + m and recursively return: suc (n + m)
template<Natural N, Natural M>
struct AddHelper<Suc<N>, M> {
	using type = Suc<typename AddHelper<N, M>::type>;
};

template<Natural N, Natural M>
using Add = typename AddHelper<N, M>::type;


static void test_natural_addition() {
	using One = Suc<Zero>;
	using Two = Suc<Suc<Zero>>;

	One x{Add<Zero, One>()};
	One y{Add<One, Zero>()};
	Two t{Add<One, One>()}; // Because a 'Two' can be initialized
	//                         from a 'Two' only, this also proves
	//                         that 1 + 1 = 2.
	// indeed:
	static_assert(std::is_same_v<Add<One, One>, Two>); // 1 + 1 = 2
	static_assert(std::is_same_v<Add<Two, One>, Suc<Two>>);
}

// ## Chapter 2
/*
 * There is a direct relationship between computer programs and
 * mathematical proofs. This property is referred to as the Curry-Howard
 * correspondence. A program is a proof and the formula it proves is the
 * type of the program.
 *
 *              Correspondence Table
 *
 * +-------------------+----------------------------+
 * |     Programs      |           Proofs           |
 * +-------------------+----------------------------+
 * | types             | judgments or propositions |
 * | values            | proofs                     |
 * | data constructors | inference rules            |
 * +-------------------+----------------------------+
 */

// For example let's say that we want to prove that 1 + 1 = 2. We encode
// the notion of equality into a type constructor that we call:
// 'Equality'.

// Equality is a type constructor that takes 2 types and generates
// another type:
// Equality : Set -> Set -> Set

// We implement Equality in C++ like this:
// First, let's *declare* the Equality type constructor:
template<typename T, typename U>
struct Equality;

// Because Equality does not have a definition (it just has a
// declaration), we can't create an object of type Equality<x, y> yet.

// Actually we won't provide a definition of 'Equality' for the general
// case. therefore we can't construct just any Equality object.

// The template specialization Equality<T, T> will provide the only
// definition for Equality. It can be regarded as a constructor that
// corresponds to the reflexivity inference rule that states that:
// ∀ x. x == x

// Equality {A : Set}(T : A) : A -> Set
// data _==_ {A : Set}(x : A) : A -> Set where
//     refl : x == x

// we write {A : Set} because the resulting type of 'Equality' denoted
// by 'Set' in the type signature will depend on a type A we write (T :
// A) to introduce in scope the variable T which is a type.

template<typename T>
struct Equality<T, T> {};

// If we are able to construct a value of type Equality with the
// parameters 1 + 1 and 2 then we've proven the equality.

// when matching template type parameters, the compiler uses an equality
// relation on types that obey the Peano axioms for natural numbers:
// reflexivity, symmetry, transitivity and closure.

// trying it out
static void equality_proof() {

	using One = Suc<Zero>;
	using Two = Suc<Suc<Zero>>;
	// auto p1 = Equality<One, Add<One, One>>(); // <- error:
	//        invalid use of incomplete type
	//        ‘struct Equality<Suc<Zero>, Suc<Suc<Zero> > >’
	auto proof1{Equality<Add<One, One>, Two>()};

	// the existence of the variable 'proof1' of type:
	// 'Equality<Two, Add<One, One>>' proves that 'Add<One, One>' and
	// 'Two' are equal.
}

// Because in C++ template parameters can be either types or values, but
// not both, the above Equality will work only for proving equality of
// types. To prove equality of values we need to encode the notion of
// values equality into another type.

// ValueEquality : (T : Set) -> T -> T -> Set
template<typename T, T val1, T val2>
struct ValueEquality;

template<typename T, T val>
struct ValueEquality<T, val, val> {};

static void value_equality_proof() {
	// 'a' == 'a'
	ValueEquality<char, 'a', 'a'>();

	// sizeof(char) == 1, just like a static_assert
	ValueEquality<size_t, sizeof(char), 1>();
}

// ## Chapter 3

/**
 * Define a datatype family to model the judgment 'n is even' for some
 * natural number 'n'. This datatype family is parameterized (indexed)
 * by types from the 'Natural' family we defined before.
 *
 * If we can create a value of this datatype for a natural number 'n'
 * then we have proven that 'n' is an even number.
 */

// data _even : ℕ → Set where
//   ZERO : zero even
//   STEP : ∀ x → x even → suc (suc x) even

// please note that 'n' from 'n even' could be inferred

// Even : Natural -> Set
// 'Even' is a type constructor that takes a 'Natural' datatype as
// parameter. This template class does not have a definition for all
// members of the 'Natural' family.

template<Natural N, typename Premise> struct Even; // declaration

// Remark: A struct or a class without a definition is analogous to a
// class definition without a constructor, but at the types level.

// EvenNatural is a constraint that checks that:
// 1. N is a Natural number
// 2. E is a specialization of Even for the type N
template<typename N, typename E>
concept EvenNatural = Natural<N>
		&& is_specialization_of_v<E, Even>
		&& std::is_same_v<N, typename E::Subject>;

// Let's provide definitions (as template specializations) to the Even
// class.

template<>
struct Even<Zero, void> {
	using Subject = Zero;
};

// ZERO : Even
// ZERO represents the axiom that Zero is even.
using ZERO = Even<Zero, void>;

template<Natural N, typename Premise>
		requires EvenNatural<N, Premise>
struct Even<Suc<Suc<N>>, Premise> {
	using Subject = Suc<Suc<N>>;
};

// STEP : {n : Natural} -> Even<n> -> Even<Suc<Suc<n>>>
// STEP represents the rule that if n is even then n + 2 is also even.
template<Natural N, typename Premise>
		requires EvenNatural<N, Premise>
using STEP = Even<Suc<Suc<N>>, Premise>;

static void even_number_proofs() {
	// proof1: Zero is even, by axiom ZERO
	ZERO(); 

	// proof2: 2 a.k.a. Suc<Suc<Zero>> is even. We use the premise ZERO
	// and apply the STEP inference rule (constructor).
	STEP<Zero, ZERO>();

	// Let's try to prove that 3 (Suc<Suc<Suc<Zero>>>) is even.
	// The ZERO axiom is no good as it proves that Zero is even, not
	// that 3 is even.
	//
	// In order to apply the STEP inference rule to prove that 3 is
	// even, we need to also provide a proof that 1 is even, that is an
	// object whose type E satisfies the EvenNatural<1, E> constraint.
	// But there is no such object.

	// STEP<Suc<Zero>, ZERO>(); <- error: template constraint
	// failure ZERO does not prove that 1 is even

	// STEP<Suc<Zero>, STEP<Zero, ZERO>>(); <- error: template
	// constraint failure, STEP<Zero, ZERO> does not prove that 1 is
	// even, it proves that 2 is even.

	// proof3: to prove that 4 is even, we apply the STEP inference rule
	// to 2 and use the premise that 2 is even i.e. STEP<Zero, ZERO>
	using Two = Suc<Suc<Zero>>;
	using Four = Suc<Suc<Two>>;

	STEP<Two, STEP<Zero, ZERO>>();

	static_assert(std::is_same_v<
					STEP<Two, STEP<Zero, ZERO>>::Subject,
					Four>);
}

} // namespace peano

// ## Chapter 4

namespace logic {

using namespace peano;

// For example if we can implement a function and it compiles, we can
// consider that we have proven the implication: given the hypotheses
// corresponding to the types of the arguments the conclusion
// corresponding to the function's return type holds.


// To prove the implication P -> Q we have to implement a function
// taking a P as a parameter and returning a Q.
template<typename P, typename Q>
struct Implication : std::function<Q(P)> {
	// inherit constructors from base class
	using std::function<Q(P)>::function;
	// disable default constructor
	Implication() = delete;
};

// Let's prove that zero is even implies that two is even
static void example_implication_proof() {
	using Two = Suc<Suc<Zero>>;
	Implication<ZERO,
				Even<Two, ZERO>
		> impl1 = [](ZERO z) {
				return STEP<Zero, decltype(z)>();
			};
}

// The generic identity function proves tautology i.e. ∀ P. P → P
template<typename P>
static P&& identity(P&& x) {
	return std::forward<P>(x);
}

// Let's model conjunction of propositions. We prove P ∧ Q by proving
// both P and Q. So conjunction is just the product type of P and Q
// (a.k.a. record, tuple, struct etc.).
// And (P Q : Set) : Set
template<typename P, typename Q>
using And = std::pair<P, Q>;

// To prove the logical equivalence P <=> Q we have to prove 2
// implications P -> Q *AND* P -> Q, that is we need to implement 2
// functions P -> Q and Q -> P
// _⇔_ : (P : Set) → (Q : Set) → Set
// a ⇔ b = (a → b) ∧ (b → a)

// We see that equivalence is a specialization of the conjunction (And),
// with parameters replaced by function types.
template<typename P, typename Q>
using Equivalence = And<Implication<P, Q>, Implication<Q, P>>;


// Now that we have defined conjunction and equivalence, let's prove that
// conjunction is commutative i.e. P ∧ Q ⇔ Q ∧ P.

// P ∧ Q → Q ∧ P
template<typename P, typename Q>
static constexpr Implication<And<P, Q>, And<Q, P>> conjunction_commutative_helper =
		[](And<P, Q> x) { return And<Q, P>(x.second, x.first); };

 // (P ∧ Q → Q ∧ P) ∧ (Q ∧ P → P ∧ Q)
template<typename P, typename Q>
static constexpr auto conjunction_commutative = And<
		decltype(conjunction_commutative_helper<P, Q>),
		decltype(conjunction_commutative_helper<Q, P>)>
		(
			conjunction_commutative_helper<P, Q>,
			conjunction_commutative_helper<Q, P>
		);

static void test_logic() {
	// using One = Suc<Zero>;
	using Two = Suc<Suc<Zero>>;

	// To prove that Even<Zero> implies Even<Zero> (a tautological implication)
	// we have to implement a function : Even<Zero> -> Even<Zero>
	Implication<ZERO, ZERO>([](ZERO x) { return x; });

	// we can use the generic identity function to prove the same thing
	// Implication<Even<Zero>, Even<Zero>> proof2(identity<Even<Zero>>);
	Implication<ZERO, ZERO> proof2(identity<ZERO>);
}

} // namespace logic

int main()
{
	using namespace peano;
	using namespace logic;

	test_naturals();
	test_natural_addition();
	equality_proof();
	value_equality_proof();
	even_number_proofs();
	example_implication_proof();
	test_logic();
	return 0;
}
