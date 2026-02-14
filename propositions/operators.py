# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    if is_variable(formula.root):
        return Formula(formula.root)
    if is_constant(formula.root):
        return Formula(formula.root)
    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))
    A = to_not_and_or(formula.first)
    B = to_not_and_or(formula.second)
    if formula.root == '&':
        return Formula('&', A, B)
    if formula.root == '|':
        return Formula('|', A, B)
    if formula.root == '->':
        return Formula('|', Formula('~', A), B)
    if formula.root == '+':
        left = Formula('&', A, Formula('~', B))
        right = Formula('&', Formula('~', A), B)
        return Formula('|', left, right)
    if formula.root == '<->':
        left = Formula('&', A, B)
        right = Formula('&', Formula('~', A), Formula('~', B))
        return Formula('|', left, right)
    if formula.root == '-&':
        return Formula('~', Formula('&', A, B))
    if formula.root == '-|':
        return Formula('~', Formula('|', A, B))
    return Formula(formula.root, A, B)
    # Task 3.5

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
