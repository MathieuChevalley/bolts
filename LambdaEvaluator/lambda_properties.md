##Term

A term is either a variable, an abstraction, an application or an substitution.

##Evaluation

For all term T, the evaluation of T is a value, that is either a variable or an abstraction.

##Strong Evaluation

For all term T, the strong evaluation of T is reduced. A reduced term is a term where all beta reduction have been applied.

##Alpha Equivalence

Two terms are alpha equivalent if they are equal upon renaming of the bound variables.

#Reflexivity

For all term t1 and t2, alpha_equivalent(t1, t2) implies alpha_equivalent(t2, t1).

##Substitution

#Uniqueness 1

For all term t1 and t2 that are equal, applying the same substition to both terms maintains equality.

#Uniqueness 2

For all term t1 and t2 that are equal, and for all subsitution s1 and s2 that are equal, applying s1 to t1 and s2 to t2 maintains euality between the two terms.

##Substitution Lemma

For all substitution s1, s2 and term t, t[s1.x = s1.m][s2.x = s2.m] == t[s2.x = s2.m][s1.x = s1.m[s2.x = s2.m]]

