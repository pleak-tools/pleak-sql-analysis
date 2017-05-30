create table logged_in_users(
  id int8 primary key,
  log_in_time int8
);

create table friends(
  id int8 primary key,
  first_name text,
  last_name text
);

