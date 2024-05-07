package com.owltest.util;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import openllet.owlapi.OpenlletReasoner;
import openllet.owlapi.OpenlletReasonerFactory;
import openllet.owlapi.SWRL;

import org.apache.http.conn.routing.RouteInfo;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.EntityType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.model.SWRLAtom;
import org.semanticweb.owlapi.model.SWRLDArgument;
import org.semanticweb.owlapi.model.SWRLLiteralArgument;
import org.semanticweb.owlapi.model.SWRLRule;
import org.semanticweb.owlapi.model.SWRLVariable;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.util.InferredAxiomGenerator;
import org.semanticweb.owlapi.util.InferredClassAssertionAxiomGenerator;
import org.semanticweb.owlapi.util.InferredDataPropertyCharacteristicAxiomGenerator;
import org.semanticweb.owlapi.util.InferredInverseObjectPropertiesAxiomGenerator;
import org.semanticweb.owlapi.util.InferredObjectPropertyCharacteristicAxiomGenerator;
import org.semanticweb.owlapi.util.InferredOntologyGenerator;
import org.semanticweb.owlapi.util.InferredPropertyAssertionGenerator;
import org.semanticweb.owlapi.util.InferredSubClassAxiomGenerator;
import org.semanticweb.owlapi.util.InferredDataPropertyAxiomGenerator;
import org.semanticweb.owlapi.vocab.SWRLBuiltInsVocabulary;

import com.owltest.models.RuleM;
import com.owltest.models.Rules;

public class OntologyUtil {

    public static SWRLRule createRule(String antecedent, String consequent, OWLOntology o) {
        
        OWLOntologyManager om = o.getOWLOntologyManager();
        OWLDataFactory factory = om.getOWLDataFactory();
        String ontologyIRI = o.getOntologyID().getOntologyIRI().get().toString();
        ArrayList<OWLClass> owlclasses = new ArrayList<OWLClass>();
        o.classesInSignature().forEach(owlclasses::add);
        ArrayList<String> classes = new ArrayList<String>();
        for (OWLClass c : owlclasses) classes.add(c.getIRI().getFragment());
        
        ArrayList<OWLDataProperty> owldataproperties = new ArrayList<OWLDataProperty>();
        o.dataPropertiesInSignature().forEach(owldataproperties::add);
        ArrayList<String> dataproperties = new ArrayList<String>();
        for (OWLDataProperty d : owldataproperties) dataproperties.add(d.getIRI().getFragment());
        
        ArrayList<OWLObjectProperty> owlobjproperties = new ArrayList<OWLObjectProperty>();
        o.objectPropertiesInSignature().forEach(owlobjproperties::add);
        ArrayList<String> objproperties = new ArrayList<String>();
        for (OWLObjectProperty ob : owlobjproperties) objproperties.add(ob.getIRI().getFragment());

        String[] bodyAtoms = antecedent.substring(0, antecedent.length()-1).split("\\)\\,\\ ");
        String headAtom = consequent.substring(0, consequent.length()-1).split("\\(")[0];
        String[] headVarib = consequent.split("\\(")[1].split("\\)")[0].split("\\,\\ ");
        Set<SWRLAtom> swrlbodyatoms = new HashSet<>();
        Set<SWRLAtom> swrlheadatoms = new HashSet<>();
        for (String ba : bodyAtoms) {
            String[] expr = ba.split("\\(");
            String atom = expr[0];
            String[] varib = expr[1].split("\\,\\ ");
            SWRLAtom a;
            if (classes.contains(atom)) {
                SWRLVariable r = SWRL.variable(IRI.create(ontologyIRI + "#" + varib[0].substring(1)));
                a = SWRL.classAtom(factory.getOWLClass(IRI.create(ontologyIRI + "#" + atom)), r);
            }
            else if (dataproperties.contains(atom)) {
                OWLDataProperty dataProperty = factory.getOWLDataProperty(IRI.create(ontologyIRI + "#" + atom));
                SWRLVariable r = SWRL.variable(IRI.create(ontologyIRI + "#" + varib[0].substring(1)));
                SWRLVariable p = SWRL.variable(IRI.create(ontologyIRI + "#" + varib[1].substring(1)));
                a = SWRL.propertyAtom(dataProperty, r, p);
            }
            else if (objproperties.contains(atom)) {
                OWLObjectProperty objectProperty = factory.getOWLObjectProperty(IRI.create(ontologyIRI + "#" + atom));
                SWRLVariable r = SWRL.variable(IRI.create(ontologyIRI + "#" + varib[0].substring(1)));
                SWRLVariable p = SWRL.variable(IRI.create(ontologyIRI + "#" + varib[1].substring(1)));
                a = SWRL.propertyAtom(objectProperty, r, p);
            }
            else {
                ArrayList<SWRLDArgument> arg = new ArrayList<SWRLDArgument>();
                for (String var : varib) {
                    if (var.contains("?")) {
                        SWRLVariable v = SWRL.variable(IRI.create(ontologyIRI + "#" + var.substring(1)));
                        arg.add(v);
                    }
                    else {
                        String temp;
                        if (var.contains("\"")) temp = var.split("\\\"")[1];
                        else temp = var;
                        try {
                            double t = Double.parseDouble(temp);
                            arg.add(SWRL.constant(t));
                          } catch(NumberFormatException e){
                            arg.add(SWRL.constant(temp));
                          }    
                    }
                    }
                a = SWRL.builtIn(SWRLBuiltInsVocabulary.getBuiltIn(IRI.create("http://www.w3.org/2003/11/swrlb#" + atom)), arg); 
            }
            swrlbodyatoms.add(a);
        }
        OWLDataProperty headProp = factory.getOWLDataProperty(IRI.create(ontologyIRI + "#" + headAtom));
        SWRLVariable a1;
        SWRLAtom a;
        a1 = SWRL.variable(IRI.create(ontologyIRI + "#" + headVarib[0].substring(1)));
        if (headVarib[1].contains("?")) {
            SWRLVariable a2 = SWRL.variable(IRI.create(ontologyIRI + "#" + headVarib[1].substring(1)));
            a = SWRL.propertyAtom(headProp, a1, a2);
        }
        else {
            if (headVarib[1].contains("?")) {
                SWRLVariable a2 = SWRL.variable(IRI.create(ontologyIRI + "#" + headVarib[1].substring(1)));
                a = SWRL.propertyAtom(headProp, a1, a2);
            }
            else{
                String var;
                if (headVarib[1].contains("\"")) var = headVarib[1].split("\\\"")[1];
                else var = headVarib[1];
                SWRLLiteralArgument a2 = SWRL.constant(var);
                a = SWRL.propertyAtom(headProp, a1, a2);
            }
        }
        swrlheadatoms.add(a);

        SWRLRule rule = SWRL.rule(swrlbodyatoms, swrlheadatoms);
        return rule;
    }
}
