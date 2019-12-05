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

CREATE TABLE person (
  person_id int8 PRIMARY KEY,
  lastname text NOT NULL,
  firstname text,
  birthdate date,
  deceased date DEFAULT NULL,
  gender text,
  residence int8 REFERENCES community NOT NULL,
  citizenship int8 REFERENCES nation NOT NULL
);

CREATE TABLE person2diseasestate(
  diseasestate text NOT NULL,
  person_id int8 REFERENCES person NOT NULL,
  transitiondate date NOT NULL
);

CREATE TABLE person2diseaseriskfactor(
  riskfactor_id int8 NOT NULL,
  person_id int8 NOT NULL
);
