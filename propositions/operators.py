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
        if formula.root == 'T':
            return Formula('|', Formula('p'), Formula('~', Formula('p')))
        return Formula('&', Formula('p'), Formula('~', Formula('p')))
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
    f = to_not_and_or(formula)
    if is_variable(f.root) or is_constant(f.root):
        return Formula(f.root)
    if is_unary(f.root):
        return Formula('~', to_not_and(f.first))
    A = to_not_and(f.first)
    B = to_not_and(f.second)
    if f.root == '&':
        return Formula('&', A, B)
    if f.root == '|':
        return Formula('~', Formula('&', Formula('~', A), Formula('~', B)))
    return Formula(f.root, A, B)
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
    f = to_not_and(formula)
    if is_variable(f.root) or is_constant(f.root):
        return Formula(f.root)
    if is_unary(f.root):
        A = to_nand(f.first)
        return Formula('-&', A, A)
    A = to_nand(f.first)
    B = to_nand(f.second)
    if f.root == '&':
        nand_ab = Formula('-&', A, B)
        return Formula('-&', nand_ab, nand_ab)
    if f.root == '|':
        na = Formula('-&', A, A)
        nb = Formula('-&', B, B)
        return Formula('-&', na, nb)
    return Formula(f.root, A, B)
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
    if is_variable(formula.root):
        return Formula(formula.root)
    if is_constant(formula.root):
        if formula.root == 'T':
            return Formula('->', Formula('p'), Formula('p'))
        return Formula('~', Formula('->', Formula('p'), Formula('p')))
    if is_unary(formula.root):
        return Formula('~', to_implies_not(formula.first))
    A = to_implies_not(formula.first)
    B = to_implies_not(formula.second)
    if formula.root == '&':
        return Formula('~', Formula('->', A, Formula('~', B)))
    if formula.root == '|':
        return Formula('->', Formula('~', A), B)
    if formula.root == '->':
        return Formula('->', A, B)
    if formula.root == '<->':
        leftimp = Formula('->', A, B)
        rightimp = Formula('->', B, A)
        return Formula('~', Formula('->', leftimp, Formula('~', rightimp)))
    if formula.root == '+':
        leftimp = Formula('->', A, B)
        rightimp = Formula('->', B, A)
        eq = Formula('~', Formula('->', leftimp, Formula('~', rightimp)))
        return Formula('~', eq)
    if formula.root == '-&':
        return Formula('->', A, Formula('~', B))
    if formula.root == '-|':
        return Formula('~', Formula('->', Formula('~', A), B))
    return Formula(formula.root, A, B)
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
    if is_variable(formula.root):
        return Formula(formula.root)
    if is_constant(formula.root):
        if formula.root == 'F':
            return Formula('F')
        return Formula('->', Formula('F'), Formula('F'))
    if is_unary(formula.root):
        return Formula('->', to_implies_false(formula.first), Formula('F'))
    A = to_implies_false(formula.first)
    B = to_implies_false(formula.second)
    if formula.root == '&':
        return Formula('->', Formula('->', A, Formula('->', B, Formula('F'))), Formula('F'))
    if formula.root == '|':
        return Formula('->', Formula('->', A, Formula('F')), B)
    if formula.root == '->':
        return Formula('->', A, B)
    if formula.root == '<->':
        leftimp = Formula('->', A, B)
        rightimp = Formula('->', B, A)
        return Formula('->', Formula('->', leftimp, Formula('->', rightimp, Formula('F'))), Formula('F'))
    if formula.root == '+':
        leftimp = Formula('->', A, B)
        rightimp = Formula('->', B, A)
        eq = Formula('->', Formula('->', leftimp, Formula('->', rightimp, Formula('F'))), Formula('F'))
        return Formula('->', eq, Formula('F'))
    if formula.root == '-&':
        and_map = Formula('->', Formula('->', A, Formula('->', B, Formula('F'))), Formula('F'))
        return Formula('->', and_map, Formula('F'))
    if formula.root == '-|':
        or_map = Formula('->', Formula('->', A, Formula('F')), B)
        return Formula('->', or_map, Formula('F'))
    return Formula(formula.root, A, B)
    # Task 3.6d
