-- IshikiConj51: Library root
-- Imports all modules for the formalisation of Ishiki Conjecture 5.1.
-- See Ishiki, "An isometric extensor of metrics", arXiv:2407.03030 (2024).

import IshikiConj51.Conj51.MetD
import IshikiConj51.Conj51.Relabel
import IshikiConj51.Conj51.Cardinality
import IshikiConj51.Conj51.GDeltaComplete
import IshikiConj51.Conj51.MetricConstruction
import IshikiConj51.Conj51.ClosedEmbedding
import IshikiConj51.Conj51.MainTheorem

-- Ishiki-extension package (Issue #47).  Layer 1: bounded star-metric coding.
import IshikiConj51.Ext.BddPMet
import IshikiConj51.Ext.BoundedCoding
import IshikiConj51.Ext.Borel
import IshikiConj51.Ext.CPM
import IshikiConj51.Ext.Relabel
import IshikiConj51.Ext.Amalgam
import IshikiConj51.Ext.Component
import IshikiConj51.Ext.GeneralSpace
import IshikiConj51.Ext.GeneralSeparability
import IshikiConj51.Ext.CompleteMetrizability
-- Issue #107: every component of `Met(X)` is non-Borel for nonseparable `X`.
import IshikiConj51.Ext.GeneralComponent
import IshikiConj51.Ext.Completeness
import IshikiConj51.Ext.CompleteMetric

-- Literal-statement coverage (Issue #96): Lemma 3.2 relative to `Met(Z)`.
import IshikiConj51.Ext.BMetClopen

-- Non-Archimedean track (Issue #81): the discrete ultrametric core, 3.10–3.13.
import IshikiConj51.Ext.UltraPMet
import IshikiConj51.Ext.CantorUltra
import IshikiConj51.Ext.UltraCoding
import IshikiConj51.Ext.UltraComponent

-- Non-Archimedean track (Issue #82): the general-space transfer, Theorem 3.14
-- and Corollary 3.15.
import IshikiConj51.Ext.UltraGeneral
import IshikiConj51.Ext.UltraTransfer

-- Non-Archimedean track (Issue #83): the complete-ultrametric branch, Theorem
-- 3.16 and Corollary 3.17.
import IshikiConj51.Ext.UltraComplete
import IshikiConj51.Ext.UltraCompleteTransfer

-- Non-Archimedean track (Issue #96): the published-interface wrappers for
-- Theorem 3.14 and Corollaries 3.15 and 3.17.
import IshikiConj51.Ext.UltraPublished
