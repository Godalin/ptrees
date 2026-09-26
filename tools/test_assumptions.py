"""Compiled-contract parser must fail closed, even if coqtop returns zero."""
import copy
import subprocess
import unittest
from unittest.mock import patch
import audit_assumptions as audit


class ParserTests(unittest.TestCase):
    def answer(self, text=None, error='', status=0):
        return subprocess.CompletedProcess([],status,text or
            'AUDIT_TYPE_0\nendpoint : True\nAUDIT_AXIOMS_0\nClosed under the global context\nAUDIT_END_0\n',error)

    def test_closed_endpoint(self):
        result=audit.parse(self.answer(),['M.endpoint'])
        self.assertEqual(result,[{'name':'M.endpoint','type':'endpoint : True',
                                 'assumptions':'Closed under the global context'}])

    def test_coq_errors_are_not_success(self):
        for result in [self.answer(error='Error: absent'),self.answer(status=1),
                       self.answer(text='Error: absent\n'+self.answer().stdout)]:
            with self.assertRaises(AssertionError): audit.parse(result,['M.endpoint'])

    def test_markers_required_once_in_order(self):
        good=self.answer().stdout
        for bad in [good.replace('AUDIT_END_0','MISSING'),good+'AUDIT_END_0\n',
                    good.replace('AUDIT_AXIOMS_0','AUDIT_TYPE_0'),
                    good.replace('endpoint : True','')]:
            with self.assertRaises(AssertionError): audit.parse(self.answer(text=bad),['M.endpoint'])

    def test_bad_assumptions(self):
        for text in ['Axioms:\nunparsed','garbage','Axioms:',
                     'Axioms:\nx : True\nx : True','Axioms:\nx : True\nunknown']:
            with self.assertRaises(AssertionError): audit.logical_axioms(text)

    def test_multiline_axiom(self):
        self.assertEqual(audit.logical_axioms('Axioms:\nCoq.ext :\n  forall x, x = x'),{'Coq.ext'})

    def test_exact_contract_detects_premise_or_axiom(self):
        original=audit.parse(self.answer(),['M.endpoint'])
        for key,value in [('type','endpoint : TransportExists -> True'),
                          ('assumptions','Axioms:\nshortcut : False')]:
            changed=copy.deepcopy(original); changed[0][key]=value
            with self.assertRaises(AssertionError): audit.compare(original,changed)
        with self.assertRaises(AssertionError): audit.compare(original,[])
        with self.assertRaises(AssertionError): audit.compare(original*2,original*2)

    def test_duplicate_query_before_coq(self):
        with patch.object(audit.subprocess,'run') as run:
            with self.assertRaises(AssertionError): audit.query(['M.x','M.x'])
            run.assert_not_called()

    def test_nested_module_requires_owning_library(self):
        self.assertEqual(audit.declaration_module(
            'PTree.Interp.FreeOmega.Rewriting.FreeOmegaRewriting.free_omega_iter_Proper'),
            'PTree.Interp.FreeOmega.Rewriting')
        self.assertEqual(audit.declaration_module(
            'PTree.Regression.Semantics.FreeOmegaRewriting.OptIn.imported_iter_proper'),
            'PTree.Regression.Semantics.FreeOmegaRewriting')
        self.assertEqual(audit.declaration_module('PTree.Eq.Algebra.peutt_bind_ret_l'),
                         'PTree.Eq.Algebra')

    def test_unknown_owner_is_not_silently_dropped(self):
        self.assertEqual(audit.declaration_module('PTree.MissingOwner.MissingModule.x'),
                         'PTree.MissingOwner.MissingModule')
        self.assertEqual(audit.declaration_module('Coq.Init.Logic.eq_refl'), 'Coq.Init.Logic')

    def test_comments_and_strings(self):
        self.assertEqual(audit.without_comments('x (* nested (* c *) *) y').split(),['x','y'])
        self.assertEqual(audit.without_comments('"(* literal *)"'),'"(* literal *)"')
        for bad in ['(* open','"open']:
            with self.assertRaises(AssertionError): audit.without_comments(bad)


if __name__=='__main__': unittest.main()
