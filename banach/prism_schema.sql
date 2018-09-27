CREATE TABLE nation (
  nation_id int8 PRIMARY KEY,
  nation_name text NOT NULL
);

CREATE TABLE community (
  community_id int8 PRIMARY KEY,
  community_name text NOT NULL,
  latitude float8,
  longitude float8,
  nation_id int8 REFERENCES nation NOT NULL
);

CREATE TABLE policyauthority (
  authority_id int8 PRIMARY KEY,
  authority text NOT NULL
);

CREATE TABLE policyauthority2community (
  authority_id int8 REFERENCES policyauthority NOT NULL,
  community_id int8 REFERENCES community NOT NULL,
  PRIMARY KEY (authority_id, community_id)
);

CREATE TABLE person (
  person_id int8 PRIMARY KEY,
  lastname text NOT NULL,
  firstname text,
  birthdate int8,
  deceased float8 DEFAULT NULL,
  gender text,
  residence int8 REFERENCES community NOT NULL,
  citizenship int8 REFERENCES nation NOT NULL
);

-- NOTE that community in this table is the destination of travel
CREATE TABLE travel (
  person_id int8 REFERENCES person NOT NULL,
  community_id int8 REFERENCES community NOT NULL,
  traveldate int8 NOT NULL
);

-- NOTE: this table declaration explicitly assumes a, S -> I -> R -> D progression, with a single
-- date for each progressive step at most. 
--
CREATE TABLE person2diseasestate(
  diseasestate text NOT NULL,
  person_id int8 REFERENCES person NOT NULL,
  transitiondate int8 NOT NULL,
  PRIMARY KEY (diseasestate, person_id)
);

CREATE TABLE person2diseaseriskfactor(
  riskfactor_id int8 NOT NULL,
  person_id int8 REFERENCES person NOT NULL,
  PRIMARY KEY (riskfactor_id, person_id)
);
