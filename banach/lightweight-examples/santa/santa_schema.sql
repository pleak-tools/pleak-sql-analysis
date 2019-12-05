Create table wishes (
  wish_id INT8,
  personname TEXT, 
  item_id INT8,
  quantity INT8);

create table items (
  item_id INT8,
  itemname TEXT, 
  color TEXT, 
  quantity INT8);

create table wish_summary (
  item_id INT8,
  need INT8);

create table missing_items (
  item_id INT8,
  itemname TEXT,
  color TEXT,
  needcount INT8);

create table res (
  res INT8);
