# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/soundness.py

"""Programmatic proof of the soundness of Propositional Logic."""

from typing import Tuple

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *

def rule_nonsoundness_from_specialization_nonsoundness(
        general: InferenceRule, specialization: InferenceRule, model: Model) \
        -> Model:
    """Demonstrates the non-soundness of the given general inference rule given
    an example of the non-soundness of the given specialization of this rule.

    Parameters:
        general: inference rule to the soundness of which to find a
            counterexample.
        specialization: non-sound specialization of `general`.
        model: model in which `specialization` does not hold.

    Returns:
        A model in which `general` does not hold.
    """
    assert specialization.is_specialization_of(general)
    assert not evaluate_inference(specialization, model)
    # Task 4.9
    spec_map = general.specialization_map(specialization)
    new_model = {}
    for var in general.variables():
        if var in spec_map:
            new_model[var] = evaluate(spec_map[var], model)
        else:
            new_model[var] = model[var]
    return new_model

def nonsound_rule_of_nonsound_proof(proof: Proof, model: Model) -> \
        Tuple[InferenceRule, Model]:
    """Finds a non-sound inference rule used by the given valid proof of a
    non-sound inference rule, and demonstrates the non-soundness of the former
    rule.

    Parameters:
        proof: valid proof of a non-sound inference rule.
        model: model in which the inference rule proved by the given proof does
            not hold.

    Returns:
        A pair of a non-sound inference rule used in the given proof and a model
        in which this rule does not hold.
    """
    assert proof.is_valid()
    assert not evaluate_inference(proof.statement, model)
    # Task 4.10
    current = len(proof.lines) - 1
    while True:
        line = proof.lines[current]
        if line.is_assumption():
            raise ValueError("Unexpected assumption line in false path")
        else:
            if not evaluate(line.formula, model):
                assumptions_true = all(evaluate(proof.lines[i].formula, model)
                                       for i in line.assumptions)
                if assumptions_true:
                    instance_assumptions = [proof.lines[i].formula
                                            for i in line.assumptions]
                    instance = InferenceRule(instance_assumptions, line.formula)
                    new_model = rule_nonsoundness_from_specialization_nonsoundness(
                        line.rule, instance, model)
                    return (line.rule, new_model)
                else:
                    for i in line.assumptions:
                        if not evaluate(proof.lines[i].formula, model):
                            current = i
                            break
                    continue
            else:
                raise ValueError("Encountered true formula in false path")
