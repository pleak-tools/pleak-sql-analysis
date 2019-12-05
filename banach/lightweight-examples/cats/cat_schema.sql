CREATE TABLE cat ( cat_id INT8 PRIMARY KEY, name TEXT,  gender TEXT, color TEXT, available BOOL);
CREATE TABLE catfood ( food_id INT8 PRIMARY KEY, color TEXT, price INT8);
CREATE TABLE catcounts (color TEXT, gender TEXT, cnt INT8);
