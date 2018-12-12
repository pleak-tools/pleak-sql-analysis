Create table wishes (
  wish_id INT8 Primary key, 
  personname TEXT, 
  item_id INT8);

create table items (
  item_id INT8 primary key, 
  itemname TEXT, 
  color TEXT, 
  quantity INT8);
